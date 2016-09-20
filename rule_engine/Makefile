all:
	g++ --std=c++14 -g -rdynamic -D_GLIBCXX_DEBUG -o flatten flattener.cpp aligner.cpp HighNode.cpp -ldw -Wall
	g++ --std=c++14 -g -O3 -o opt_flatten flattener.cpp aligner.cpp HighNode.cpp -DNO_BACKWARD -D_GLIBCXX_DEBUG -Wall
	g++ --std=c++14 -O3 -g -rdynamic -D_GLIBCXX_DEBUG -o reprinter rules_reprinter.cpp -ldw
	g++ --std=c++14 -O3 -g -rdynamic -D_GLIBCXX_DEBUG -o recompressor recompressor.cpp HighNode.cpp -DNO_BACKWARD -ldw -Wall
