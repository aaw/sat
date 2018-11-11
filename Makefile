CPPFLAGS=-g -O3 -Werror -Wall -std=c++11 -DLOGGING
LDFLAGS=-g
LDLIBS=
RM=rm -f

sat: main.o parse.o solve.o
	g++ $(LDFLAGS) -o bin/sat bin/main.o bin/parse.o bin/solve.o $(LDLIBS)

main.o: src/main.cc src/parse.h src/logging.h src/solve.h
	g++ $(CPPFLAGS) -c src/main.cc -o bin/main.o

parse.o: src/parse.cc src/parse.h src/logging.h
	g++ $(CPPFLAGS) -c src/parse.cc -o bin/parse.o

solve.o: src/solve.cc src/solve.h src/logging.h
	g++ $(CPPFLAGS) -c src/solve.cc -o bin/solve.o

clean:
	$(RM) bin/*.o

distclean: clean
	$(RM) bin/sat
