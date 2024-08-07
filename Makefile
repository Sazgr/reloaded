EXE = exocet
EVALFILE = src/default.nn

SOURCES := src/*.cpp

CXX := g++

CXXFLAGS := -pthread -std=c++17 -O3 -ffast-math -DNDEBUG -Wl,--stack,33554432 -march=native -static -DNETWORK_FILE=\"$(EVALFILE)\"

LINKER :=

SUFFIX :=

ifeq ($(OS), Windows_NT)
	SUFFIX := .exe
else
	SUFFIX :=
	LINKER := -lm
endif

OUT := $(EXE)$(SUFFIX)


$(EXE): $(SOURCES)
	$(CXX) $^ $(CXXFLAGS) -o $(OUT) $(LINKER) 
