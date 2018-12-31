CPPFLAGS=-g -O3 -Werror -Wall -std=c++11 -DLOGGING
LDFLAGS=-g
LDLIBS=
RM=rm -f

all: bin/btwl bin/dpll

bin/btwl: src/btwl.cc src/logging.h src/types.h src/flags.h
	g++ $(CPPFLAGS) -o bin/btwl src/btwl.cc $(LDLIBS)

bin/dpll: src/dpll.cc src/logging.h src/types.h src/flags.h
	g++ $(CPPFLAGS) -o bin/dpll src/dpll.cc $(LDLIBS)

clean:
	$(RM) bin/*
	$(RM) *~
	$(RM) */*~
