CC=g++
CPPFLAGS=-g -O3 -Werror -Wall -Wno-psabi -mtune=native -march=native -std=c++11
ifndef OPT
CPPFLAGS += -DLOGGING -DCOUNTERS -DTIMERS
endif
LDFLAGS=-g
LDLIBS=
RM=rm -f

all: bin/btwl bin/dpll bin/cdcl bin/look bin/walk

check: all
	script/test.sh -bbtwl
	script/test.sh -bdpll
	script/test.sh -bcdcl
	script/test.sh -bcdcl -dmedium
	script/test.sh -blook
	script/test.sh -blook -dmedium
	script/test.sh -bwalk -lsat
	script/test.sh -bwalk -lsat -dmedium
	script/fuzz.sh -s1

test: tbin/heap_test

bin/btwl: src/btwl.cc src/logging.h src/types.h src/flags.h src/timer.h src/counters.h src/params.h src/parse.h src/process.h
	$(CC) $(CPPFLAGS) -o bin/btwl src/btwl.cc $(LDLIBS)

bin/cdcl: src/cdcl.cc src/logging.h src/types.h src/flags.h src/heap.h src/timer.h src/counters.h src/params.h src/parse.h src/process.h
	$(CC) $(CPPFLAGS) -DPROOFLOG -o bin/cdcl src/cdcl.cc $(LDLIBS)

bin/dpll: src/dpll.cc src/logging.h src/types.h src/flags.h src/timer.h src/counters.h src/params.h src/parse.h src/process.h
	$(CC) $(CPPFLAGS) -o bin/dpll src/dpll.cc $(LDLIBS)

bin/look: src/look.cc src/logging.h src/types.h src/flags.h src/heap.h src/timer.h src/counters.h src/params.h src/parse.h src/process.h
	$(CC) $(CPPFLAGS) -o bin/look src/look.cc $(LDLIBS)

bin/walk: src/walk.cc src/logging.h src/types.h src/flags.h src/timer.h src/counters.h src/params.h src/parse.h src/process.h
	$(CC) $(CPPFLAGS) -o bin/walk src/walk.cc $(LDLIBS)

tbin/heap_test: src/heap_test.cc src/heap.h
	$(CC) $(CPPFLAGS) -o tbin/heap_test src/heap_test.cc $(LDLIBS)

clean:
	$(RM) bin/btwl
	$(RM) bin/cdcl
	$(RM) bin/dpll
	$(RM) bin/look
	$(RM) bin/walk
	$(RM) tbin/*
	$(RM) *~
	$(RM) */*~
