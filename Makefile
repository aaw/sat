CPPFLAGS=-g -O3 -Werror -Wall -std=c++11 -DLOGGING
LDFLAGS=-g
LDLIBS=
RM=rm -f

btwl: src/logging.h
	g++ $(CPPFLAGS) -o bin/btwl src/btwl.cc $(LDLIBS)

clean:
	$(RM) bin/*
