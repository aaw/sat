CPPFLAGS=-g -O3 -Wall -std=c++11 -DLOGGING
LDFLAGS=-g
LDLIBS=
RM=rm -f

sat: main.o parse.o
	g++ $(LDFLAGS) -o sat main.o parse.o $(LDLIBS)

main.o: main.cc parse.h logging.h
	g++ $(CPPFLAGS) -c main.cc

parse.o: parse.cc parse.h logging.h
	g++ $(CPPFLAGS) -c parse.cc

clean:
	$(RM) *.o

distclean: clean
	$(RM) sat
