#include "attacks.h"
#include "params.h"
#include "search.h"
#include "uci.h"
#include <cmath>

int lmr_table[256][256] {};

bool see(Position& position, Move move, const int threshold) {
    int to = move.end();
    int from = move.start();
    int target = position.board[to];
    //making the move and not losing it must beat the threshold
    int value = see_value[target >> 1] - threshold;
    if (move.flag() > none && move.flag() < q_castling) return true;
    if (value < 0) return false;
    int attacker = position.board[from];
    //trivial if we still beat the threshold after losing the piece
    value -= see_value[attacker >> 1];
    if (value >= 0)
        return true;
    //it doesn't matter if the to square is occupied or not
    u64 occupied = position.occupied ^ (1ull << from) ^ (1ull << to);
    u64 attackers = position.attacks_to(to, occupied);
    u64 bishops = position.pieces[4] | position.pieces[5] | position.pieces[8] | position.pieces[9];
    u64 rooks = position.pieces[6] | position.pieces[7] | position.pieces[8] | position.pieces[9];
    int side = (attacker & 1) ^ 1;
    u64 side_pieces[2] = {position.pieces[0] | position.pieces[2] | position.pieces[4] | position.pieces[6] | position.pieces[8] | position.pieces[10], position.pieces[1] | position.pieces[3] | position.pieces[5] | position.pieces[7] | position.pieces[9] | position.pieces[11]};
    //make captures until one side runs out, or fail to beat threshold
    while (true) {
        //remove used pieces from attackers
        attackers &= occupied;
        u64 my_attackers = attackers & side_pieces[side];
        if (!my_attackers) {
            break;
        }
        //pick next least valuable piece to capture with
        int piece_type;
        for (piece_type = 0; piece_type < 6; ++piece_type) {
            if (my_attackers & position.pieces[2 * piece_type + side]) break;
        } 
        side = !side;
        value = -value - 1 - see_value[piece_type];
        //value beats threshold, or can't beat threshold (negamaxed)
        if (value >= 0) {
            if (piece_type == 5 && (attackers & side_pieces[side]))
                side = !side;
            break;
        }
        //remove the used piece from occupied
        occupied ^= (1ull << (get_lsb(my_attackers & (position.pieces[2 * piece_type] | position.pieces[2 * piece_type + 1]))));
        if (piece_type == 0 || piece_type == 2 || piece_type == 4)
            attackers |= bishop_attacks(occupied, to) & bishops;
        if (piece_type == 3 || piece_type == 4)
            attackers |= rook_attacks(occupied, to) & rooks;
    }
    return side != (attacker & 1);
}

int qsearch(Position& position, Search_stack* ss, Search_data& sd, int alpha, int beta) {
    if ((*sd.timer).stopped() || (!(sd.nodes & 4095) && (*sd.timer).check(sd.nodes, 0))) return 0;
    bool in_check = position.check();
    Entry entry = sd.hash_table->probe(position.hashkey());
    bool tt_hit = entry.type() != tt_none && entry.full_hash == position.hashkey();
    if (ss->excluded.is_null() && tt_hit && (entry.type() == tt_exact || (entry.type() == tt_alpha && entry.score() <= alpha) || (entry.type() == tt_beta && entry.score() >= beta))) {
        return std::clamp(entry.score(), -18000, 18000);
    }
    int static_eval = in_check ? -20001 : position.static_eval(*sd.nnue);
    if (in_check) position.nnue_update_accumulator(*sd.nnue);
    if (!in_check) static_eval += sd.move_order->correction_value(position.pawn_hashkey(), position.side_to_move);
    int score = -20001;
    int best_score = -20001;
    if (!in_check) { //stand pat
        if (static_eval >= beta) return static_eval;
        if (static_eval > best_score) best_score = static_eval;
        if (static_eval > alpha) alpha = static_eval;
    }
    int legal_moves = 0;
    Move best_move{};
    Movelist movelist;
    if (in_check) {
        position.generate_stage<all>(movelist);
        for (int i{}; i < movelist.size(); ++i) {
            if (tt_hit && movelist[i] == entry.move()) {
                movelist[i].add_sortkey(30000);
            } else {
                movelist[i].add_sortkey(0);
            }
        }
        movelist.sort(0, movelist.size());
    } else {
        position.generate_stage<noisy>(movelist);
        for (int i{}; i < movelist.size(); ++i) {
            if (tt_hit && movelist[i] == entry.move()) {
                movelist[i].add_sortkey(30000);
            } else {
            movelist[i].add_sortkey(10000 + sd.move_order->caphist_score(movelist[i]));
            }
        }
        movelist.sort(0, movelist.size());
    }
    for (int i{}; i < movelist.size(); ++i) {
        if (!position.is_legal(movelist[i])) continue;
        if (!in_check && !see(position, movelist[i], -274)) continue;
        position.make_move<true>(movelist[i], sd.nnue);
        ss->move = movelist[i];
        bool gives_check = position.check();
        ++sd.nodes;
        ++legal_moves;
        (ss + 1)->ply = ss->ply + 1;
        score = -qsearch(position, ss + 1, sd, -beta, -alpha);
        position.undo_move<true>(movelist[i], sd.nnue);
        if ((*sd.timer).stopped()) return 0;
        if (score > best_score) {
            best_score = score;
             if (score > alpha) {
                alpha = score;
                best_move = movelist[i];
                if (score > beta) {
                    for (int j{0}; j<i; ++j) {
                        if (movelist[j].captured() != 12) {
                            sd.move_order->caphist_update(movelist[j], -1);
                        }
                    }
                    if (best_move.captured() != 12) {
                        sd.move_order->caphist_update(best_move, 1);
                    }
                    if (!in_check && (best_move == Move{} || best_move.captured() == 12) && !(best_score >= beta && best_score <= static_eval) && !(best_move == Move{} && best_score >= static_eval)) {
                        int correction_diff = std::clamp(best_score - static_eval, -256, 256);
                        sd.move_order->correction_update(position.pawn_hashkey(), position.side_to_move, correction_diff, 1);
                    }
                    sd.hash_table->insert(position.hashkey(), best_score, tt_beta, best_move, 0);
                    return score;
                }
            }
        }
    }
    if (in_check && legal_moves == 0) {
        return -20000 + ss->ply;
    }
    if (!sd.timer->stopped() && !in_check && (best_move == Move{} || best_move.captured() == 12) && !(best_score >= beta && best_score <= static_eval) && !(best_move == Move{} && best_score >= static_eval)) {
        int correction_diff = std::clamp(best_score - static_eval, -256, 256);
        sd.move_order->correction_update(position.pawn_hashkey(), position.side_to_move, correction_diff, 1);
    }
    if (!sd.timer->stopped()) {
        sd.hash_table->insert(position.hashkey(), best_score, tt_alpha, best_move, 0);
    }
    return (*sd.timer).stopped() ? 0 : best_score;
}

int search(Position& position, Search_stack* ss, Search_data& sd, int depth, int alpha, int beta, bool cutnode) {
    sd.hash_table->prefetch(position.hashkey());
    bool is_root = (ss->ply == 0);
    bool is_pv = (beta - alpha) != 1;
    if ((*sd.timer).stopped() || (!(sd.nodes & 4095) && (*sd.timer).check(sd.nodes, 0))) return 0;
    if (depth <= 0) {
        return qsearch(position, ss, sd, alpha, beta);
    }
    if (depth == 1 && is_pv) sd.pv_table[ss->ply + 1][0] = Move{};
    if (position.draw(ss->ply > 2 ? 1 : 2)) {
        sd.pv_table[ss->ply][0] = Move{};
        return 0;
    }
    bool in_check = position.check();
    Entry entry = sd.hash_table->probe(position.hashkey());
    bool tt_hit = entry.type() != tt_none && entry.full_hash == position.hashkey();
    if (!is_pv && ss->excluded.is_null() && tt_hit && entry.depth() >= depth && (entry.type() == tt_exact || (entry.type() == tt_alpha && entry.score() <= alpha) || (entry.type() == tt_beta && entry.score() >= beta))) {
        return std::clamp(entry.score(), -18000, 18000);
    }
    int static_eval = in_check ? -20001 : position.static_eval(*sd.nnue);
    if (in_check) position.nnue_update_accumulator(*sd.nnue);
    if (!in_check) static_eval += sd.move_order->correction_value(position.pawn_hashkey(), position.side_to_move);
    if (tt_hit && (entry.type() == tt_exact || (entry.type() == tt_alpha && entry.score() <= static_eval) || (entry.type() == tt_beta && entry.score() >= static_eval))) {
        static_eval = std::clamp(entry.score(), -18000, 18000);
    }
    ss->static_eval = static_eval;
    int score = -20001;
    int best_score = -20001;
    ss->double_extensions = (is_root ? 0 : (ss - 1)->double_extensions);
    int legal_moves = 0;
    Move best_move{};
    Movelist movelist;
    int tt_flag = tt_alpha;
    bool improving = !in_check && ss->excluded.is_null() && (ss - 2)->static_eval != -20001 && ss->static_eval > (ss - 2)->static_eval;
    if (depth < 8 && !(ss - 1)->move.is_null() && !is_pv && !in_check && ss->excluded.is_null() && beta > -18000 && (static_eval - rfp_base - rfp_margin * (depth - improving) >= beta)) {
        return static_eval;
    }
    if (depth > 2 && !(ss - 1)->move.is_null() && !is_pv && !in_check && ss->excluded.is_null() && beta > -18000 && static_eval > beta) {
        position.make_null();
        ss->move = Move{};
        ++sd.nodes;
        (ss + 1)->ply = ss->ply + 1;
        int r = 2 + depth / 4 + improving + std::sqrt(static_eval - beta) / 12;
        score = -search(position, ss + 1, sd, std::max(0, depth - 1 - r), -beta, -beta + 1, !cutnode);
        position.undo_null();
        if (!sd.timer->stopped() && score >= beta) {
            return (abs(score) > 18000 ? beta : score);
        }
    }
    if (depth < 4 && !is_pv && !in_check && ss->excluded.is_null() && static_eval + rzr_base + rzr_margin * depth * depth <= alpha) {
        score = qsearch(position, ss, sd, alpha, beta);
        if (score <= alpha) {
            return score;
        }
    }
    int probcut_beta = beta + pbc_margin;
    if (!is_pv && depth >= 4 && ss->excluded.is_null() && abs(beta) < 18000 && (!tt_hit || static_eval >= probcut_beta || entry.depth() < depth - 3)) {
        Movelist capture_list;
        position.generate_stage<noisy>(capture_list);
        for (int i = 0; i < capture_list.size(); ++i) {
            capture_list[i].add_sortkey(capture_list[i].mvv_lva());
        }
        capture_list.sort(0, capture_list.size());
        int probcut_result = 0;
        for (int i = 0; i < capture_list.size(); ++i) {
            if (capture_list[i] == entry.move()) continue;
            if (!position.is_legal(capture_list[i])) continue;
            if (!see(position, capture_list[i], 1)) continue;
            ss->move = capture_list[i];
            ++sd.nodes;
            (ss + 1)->ply = ss->ply + 1;
            position.make_move<true>(capture_list[i], sd.nnue);
            probcut_result = -qsearch(position, ss + 1, sd, -probcut_beta, -probcut_beta + 1);
            if (probcut_result >= probcut_beta) {
                probcut_result = -search(position, ss + 1, sd, depth - 4, -probcut_beta, -probcut_beta + 1, !cutnode);
            }
            position.undo_move<true>(capture_list[i], sd.nnue);
            if (probcut_result >= probcut_beta) {
                sd.hash_table->insert(position.hashkey(), probcut_result, tt_beta, capture_list[i], depth - 3);
                return probcut_result;
            }
        }
    }
    if (in_check) ++depth;
    if (!is_pv && depth >= 6 && !(tt_hit && !entry.move().is_null())) depth--;
    position.generate_stage<all>(movelist);
    for (int i{}; i < movelist.size(); ++i) {
        if (tt_hit && movelist[i] == entry.move()) {
            movelist[i].add_sortkey(30000);
        } else if (movelist[i].captured() != 12) {
            movelist[i].add_sortkey(5000 + 20000 * see(position, movelist[i], -274) + sd.move_order->caphist_score(movelist[i]));
        } else {
            int sort_score = 15000;
            sort_score += sd.move_order->history_score(movelist[i]) / 2;
            sort_score += sd.move_order->butterfly_score(movelist[i]) / 2;
            sort_score += sd.move_order->continuation_score((ss - 2)->move, movelist[i]) / 2;
            sort_score += sd.move_order->continuation_score((ss - 1)->move, movelist[i]) / 2;
            if (movelist[i] == sd.move_order->killer_move(ss->ply, 0)) sort_score += klr_bonus_0;
            if (movelist[i] == sd.move_order->killer_move(ss->ply, 1)) sort_score += klr_bonus_1;
            movelist[i].add_sortkey(sort_score);
        }
    }
    movelist.sort(0, movelist.size());
    for (int i{}; i < movelist.size(); ++i) {
        if (movelist[i] == ss->excluded) continue;
        if (!position.is_legal(movelist[i])) continue;
        if (!is_root && best_score > -18000) {
            if (movelist[i].captured() == 12 && !see(position, movelist[i], -spr_quiet_threshold * depth * depth)) continue;
        }
        int extension = 0;
        if (movelist[i] == entry.move() && !is_root && depth >= 6 && (entry.type() == tt_exact || entry.type() == tt_beta) && abs(entry.score()) < 18000 && entry.depth() >= depth - 3) {
            int singular_beta = entry.score() - depth * sxt_margin / 16;
            int singular_depth = (depth - 1) / 2;
            ss->excluded = movelist[i];
            int singular_score = search(position, ss, sd, singular_depth, singular_beta - 1, singular_beta, cutnode);
            ss->excluded = Move{};
            if (singular_score < singular_beta) {
                if (!is_pv && singular_score < singular_beta - dxt_margin && ss->double_extensions <= 4) {
                    extension = 2;
                    ++ss->double_extensions;
                } else {
                    extension = 1;
                }
            } else if (singular_beta >= beta) {
                return singular_beta;
            } else if (cutnode) {
                extension = -2;
            } else if (entry.score() >= beta) {
                extension = -1;
            }
            if (extension < 0) cutnode = true;
        }
        position.make_move<true>(movelist[i], sd.nnue);
        ss->move = movelist[i];
        bool gives_check = position.check();
        u64 prev_nodes = sd.nodes;
        if (depth < 8 && !in_check && !gives_check && best_score > -18000 && legal_moves >= static_cast<int>(((lmp_base / 100.0) + (lmp_margin / 100.0) * depth * depth) / ((lmp_improving / 100.0) - improving))) {
            position.undo_move<true>(movelist[i], sd.nnue);
            break;
        }
        ++sd.nodes;
        ++legal_moves;
        (ss + 1)->ply = ss->ply + 1;
        int reduction = 0;
        if (depth > 2 && legal_moves > 2 + 2 * is_pv && movelist[i].sortkey() < 20000) {
            reduction = lmr_table[legal_moves][depth];
            if (is_pv) --reduction;
            if (in_check) --reduction;
            if (!improving) ++reduction;
            if (cutnode) ++reduction;
            if (movelist[i].captured() != 12) reduction -= 1 + std::clamp(static_cast<int>(movelist[i].sortkey() - 5000 + chl_divisor / 2) / chl_divisor, -2, 2);
            if (movelist[i].captured() == 12) reduction -= std::clamp(static_cast<int>(movelist[i].sortkey() - 15000 + hsl_divisor / 2) / hsl_divisor, -2, 2);
            reduction = std::clamp(reduction, 0, depth - 2); //ensure that lmr reduction does not drop into quiescence search
        }
        if (legal_moves == 1) {
            score = -search(position, ss + 1, sd, depth - 1 + extension, -beta, -alpha, false);
        } else {
            score = -search(position, ss + 1, sd, depth - 1 - reduction + extension, -alpha - 1, -alpha, true);
            if (score > alpha && reduction) {
                score = -search(position, ss + 1, sd, depth - 1 + extension, -alpha - 1, -alpha, !cutnode);
            }
            if (score > alpha && is_pv) {
                score = -search(position, ss + 1, sd, depth - 1 + extension, -beta, -alpha, false);
            }
        }
        position.undo_move<true>(movelist[i], sd.nnue);
        if ((*sd.timer).stopped()) return 0;
        if (is_root) sd.move_order->move_nodes[movelist[i].start()][movelist[i].end()] += sd.nodes - prev_nodes;
        if (score > best_score) {
            best_score = score;
             if (score > alpha) {
                alpha = score;
                best_move = movelist[i];
                tt_flag = tt_exact;
                if (is_pv) {
                    sd.pv_table[ss->ply][0] = best_move;
                    memcpy(&sd.pv_table[ss->ply][1], &sd.pv_table[ss->ply + 1][0], sizeof(Move) * 127);
                }
                if (score > beta) {
                    for (int j{0}; j<i; ++j) {
                        if (movelist[j].captured() == 12) {
                            sd.move_order->history_update(movelist[j], -(depth + 1) * (depth + 1));
                            sd.move_order->butterfly_update(movelist[j], -(depth + 1) * (depth + 1));
                            sd.move_order->continuation_update((ss - 2)->move, movelist[j], -(depth + 1) * (depth + 1));
                            sd.move_order->continuation_update((ss - 1)->move, movelist[j], -(depth + 1) * (depth + 1));
                        } else {
                            sd.move_order->caphist_update(movelist[j], -(depth + 1) * (depth + 1));
                        }
                    }
                    if (best_move.captured() == 12) {
                        sd.move_order->history_update(best_move, (depth + 1) * (depth + 1));
                        sd.move_order->butterfly_update(best_move, (depth + 1) * (depth + 1));
                        sd.move_order->continuation_update((ss - 2)->move, best_move, (depth + 1) * (depth + 1));
                        sd.move_order->continuation_update((ss - 1)->move, best_move, (depth + 1) * (depth + 1));
                        sd.move_order->killer_update(best_move, ss->ply);
                    } else {
                        sd.move_order->caphist_update(best_move, (depth + 1) * (depth + 1));
                    }
                    if (!in_check && (best_move == Move{} || best_move.captured() == 12) && !(best_score >= beta && best_score <= static_eval) && !(best_move == Move{} && best_score >= static_eval)) {
                        int correction_diff = std::clamp(best_score - static_eval, -256, 256);
                        sd.move_order->correction_update(position.pawn_hashkey(), position.side_to_move, correction_diff, std::min(depth + 1, 16));
                    }
                    if (ss->excluded.is_null()) sd.hash_table->insert(position.hashkey(), best_score, tt_beta, best_move, depth);
                    return score;
                }
            }
        }
    }
    if (legal_moves == 0) {
        sd.pv_table[ss->ply][0] = Move{};
        if (in_check) return -20000 + ss->ply;
        else return 0;
    }
    if (!sd.timer->stopped() && !in_check && (best_move == Move{} || best_move.captured() == 12) && !(best_score >= beta && best_score <= static_eval) && !(best_move == Move{} && best_score >= static_eval)) {
        int correction_diff = std::clamp<int>(best_score - static_eval, -crh_limit, crh_limit);
        sd.move_order->correction_update(position.pawn_hashkey(), position.side_to_move, correction_diff, std::min(depth + 1, 16));
    }
    if (ss->excluded.is_null() && !sd.timer->stopped()) {
        sd.hash_table->insert(position.hashkey(), best_score, tt_flag, best_move, depth);
    }
    return (*sd.timer).stopped() ? 0 : best_score;
}

void search_root(Position& position, Limit_timer& timer, Search_data& sd, bool output) {
    Search_stack ss[96];
    ss[4].ply = 0;
    NNUE nnue;
    nnue.refresh(position);
    sd.nnue = &nnue;
    sd.timer = &timer;
    int score;
    int stability = 0;
    Move best_move = Move{};
    Movelist movelist;
    position.generate_stage<all>(movelist);
    for (int i{}; i < movelist.size(); ++i) {
        if (!position.is_legal(movelist[i])) continue;
        best_move = movelist[i];
        break;
    }
    for (int i{}; i < 64; ++i) {
        for (int j{}; j < 64; ++j) {
            sd.move_order->move_nodes[i][j] = 0;
        }
    }
    for (int depth = 1; depth < 64; ++depth) {
        double node_time_scale = depth < 3 ? 1.0 : std::clamp(((ntm_base / 100.0) - static_cast<double>(sd.move_order->move_nodes[best_move.start()][best_move.end()]) / std::max<double>(sd.nodes, 1)) * (ntm_multiplier / 100.0), ntm_minimum / 100.0, ntm_maximum / 100.0);
        double best_move_time_scale = best_move_stability[stability];
        double time_scale = node_time_scale * best_move_time_scale;
        if (timer.check(sd.nodes, depth)) break;
        if (timer.check(sd.nodes, depth, true, time_scale)) break;
        int delta = asp_initial;
        int alpha = -20001;
        int beta = 20001;
        if (depth >= 2) {
            alpha = std::max(score - delta, -20001);
            beta = std::min(score + delta,  20001);
        }
        int asp_reduction{};
        while (!timer.stopped()) {
            score = search(position, &ss[4], sd, std::max(depth - asp_reduction, 1), alpha, beta, false);
            if (timer.stopped()) {
                break;
            }
            if (score > alpha && score < beta) {
                if (sd.pv_table[0][0] == best_move) {
                    stability = std::min(stability + 1, 4);
                } else {
                    stability = 0;
                }
                break;
            }
            if (score <= alpha) {
                asp_reduction = 0;
                beta = (alpha + beta) / 2;
                alpha = std::max(score - delta, -20001);
            }
            if (score >= beta) {
                asp_reduction = std::min(asp_reduction + 1, 4);
                beta = std::min(score + delta, 20001);
            }
            delta = delta * asp_multiplier / 100;
        }
        if (timer.stopped()) {
            if (!sd.pv_table[0][0].is_null()) {
                best_move = sd.pv_table[0][0];
            }
            break;
        }
        best_move = sd.pv_table[0][0];
        if (output) print_info(score, depth, sd.nodes, static_cast<int>(sd.nodes / timer.elapsed()), static_cast<int>(timer.elapsed() * 1000), sd.pv_table[0]);
    }
    if (output) std::cout << "bestmove " << best_move << std::endl;
    sd.nnue = nullptr;
    sd.timer = nullptr;
}
