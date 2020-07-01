CPPFLAGS=-g -O3 -Werror -Wall -mtune=native -march=native -std=c++11
ifndef OPT
CPPFLAGS += -DLOGGING -DCOUNTERS -DTIMERS
endif
LDFLAGS=-g
LDLIBS=
RM=rm -f

all: bin/btwl bin/dpll bin/cdcl bin/look bin/walk

test: tbin/heap_test

bin/btwl: src/btwl.cc src/logging.h src/types.h src/flags.h src/timer.h src/counters.h src/params.h src/parse.h src/process.h
	g++ $(CPPFLAGS) -o bin/btwl src/btwl.cc $(LDLIBS)

bin/cdcl: src/cdcl.cc src/logging.h src/types.h src/flags.h src/heap.h src/timer.h src/counters.h src/params.h src/parse.h src/process.h
	g++ $(CPPFLAGS) -DPROOFLOG -o bin/cdcl src/cdcl.cc $(LDLIBS)

bin/dpll: src/dpll.cc src/logging.h src/types.h src/flags.h src/timer.h src/counters.h src/params.h src/parse.h src/process.h
	g++ $(CPPFLAGS) -o bin/dpll src/dpll.cc $(LDLIBS)

bin/look: src/look.cc src/logging.h src/types.h src/flags.h src/heap.h src/timer.h src/counters.h src/params.h src/parse.h src/process.h
	g++ $(CPPFLAGS) -o bin/look src/look.cc $(LDLIBS)

bin/walk: src/walk.cc src/logging.h src/types.h src/flags.h src/timer.h src/counters.h src/params.h src/parse.h src/process.h
	g++ $(CPPFLAGS) -o bin/walk src/walk.cc $(LDLIBS)

tbin/heap_test: src/heap_test.cc src/heap.h
	g++ $(CPPFLAGS) -o tbin/heap_test src/heap_test.cc $(LDLIBS)

clean:
	$(RM) bin/btwl
	$(RM) bin/cdcl
	$(RM) bin/dpll
	$(RM) bin/look
	$(RM) bin/walk
	$(RM) tbin/*
	$(RM) *~
	$(RM) */*~
