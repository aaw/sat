CPPFLAGS=-g -O3 -Werror -Wall -std=c++11 -DLOGGING
LDFLAGS=-g
LDLIBS=
RM=rm -f

sat: main.o parse.o solve.o
	g++ $(LDFLAGS) -o sat main.o parse.o solve.o $(LDLIBS)

main.o: main.cc parse.h logging.h
	g++ $(CPPFLAGS) -c main.cc

parse.o: parse.cc parse.h logging.h
	g++ $(CPPFLAGS) -c parse.cc

solve.o: solve.cc solve.h logging.h
	g++ $(CPPFLAGS) -c solve.cc

clean:
	$(RM) *.o

distclean: clean
	$(RM) sat
