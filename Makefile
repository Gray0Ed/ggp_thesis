all:
	g++ --std=c++14 -g -rdynamic -D_GLIBCXX_DEBUG -o flatten flattener.cpp -ldw -Wall
	g++ --std=c++14 -g -O3 -o opt_flatten flattener.cpp -DNO_BACKWARD -D_GLIBCXX_DEBUG
	#g++ --std=c++14 -g -rdynamic -D_GLIBCXX_DEBUG -o reprinter rules_reprinter.cpp -ldw

