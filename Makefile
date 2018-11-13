CPPFLAGS=-g -O3 -Werror -Wall -std=c++11 -DLOGGING
LDFLAGS=-g
LDLIBS=
RM=rm -f

sat: src/logging.h
	g++ $(CPPFLAGS) -o bin/sat src/btwl.cc $(LDLIBS)

clean:
	$(RM) bin/*
