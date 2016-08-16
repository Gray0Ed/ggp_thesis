all:
	g++ --std=c++14 -g -rdynamic -D_GLIBCXX_DEBUG -o flatten flattener.cpp -ldw
	g++ --std=c++14 -g -rdynamic -D_GLIBCXX_DEBUG -o reprinter rules_reprinter.cpp -ldw

