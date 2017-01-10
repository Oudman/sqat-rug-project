module sqat::series1::A1_SLOC

import IO;
import util::FileSystem;
import ParseTree;
import String;
import lang::java::\syntax::Java15;

/* 

Count Source Lines of Code (SLOC) per file:
- ignore comments
- ignore empty lines

Tips
- use locations with the project scheme: e.g. |project:///jpacman/...|
- functions to crawl directories can be found in util::FileSystem
- use the functions in IO to read source files

Answer the following questions:
- what is the biggest file in JPacman?
  A: That is |project://jpacman-framework/src/main/java/nl/tudelft/jpacman/level/Level.java|, with 179 SLOC
- what is the total size of JPacman?
  A: The total size of JPacman is 1901 SLOC
- is JPacman large according to SIG maintainability?
  A: Since JPacman has 1901 SLOC, it is considered to be very small (++)
- what is the ratio between actual code and test code size?
  A: The directory |project://jpacman-framework/src/test/java/nl/tudelft/jpacman| consists of 557 SLOC. The ratio between actual code and test code is therefore 901/557=3.41.

Sanity checks:
- write tests to ensure you are correctly skipping multi-line comments
- and to ensure that consecutive newlines are counted as one.
- compare you results to external tools sloc and/or cloc.pl

Bonus:
- write a hierarchical tree map visualization using vis::Figure and 
  vis::Render quickly see where the large files are. 
  (https://en.wikipedia.org/wiki/Treemapping) 

*/

alias SLOC = map[loc file, int sloc];

int sloc(loc project) {
	result = [SLOCinFile(f) | /file(f) <- crawl(project), f.extension == "java"];
	return sum(result);
}

lrel[int sloc, loc file] slocPerProjectfile(loc project) {
	result = [<SLOCinFile(f), f> | /file(f) <- crawl(project), f.extension == "java"];
	result = sort(result, bool (<int a, loc _>, <int b, loc _>) { return a > b; });
	return result;
}

int SLOCinFile(loc file){
	bool inMLC = false; // multiline comment
	bool inSTR = false; // (multiline) string in code
	bool hasCode = false;
	int numSLOC = 0;
	int char, i, j, firstQ, firstMLC, firstSLC, posdif;
	str iline;
	list[str] lines = readFileLines(file);
	for( str line <- lines){
		iline = line;
		char = 0;
		hasCode = false;
		while (char < size(line)){
			line = substring(line, char);
			if (inSTR) { // current position in current line is part of a (multiline) string
				firstQ = findFirst(line, "\"");
				if (firstQ < 0) { // not closing the string, done with this line
					char = size(line);
				} else { // possible closing of string
					if (firstQ==0 || (firstQ==1 && substring(line, firstQ-1, firstQ)!="\\") || (firstQ>1 && (substring(line, firstQ-1, firstQ)!="\\" || (substring(line, firstQ-1, firstQ)=="\\" && substring(line, firstQ-2, firstQ-1)=="\\")))) {
						inSTR = false; // string is closed
					}
					char = firstQ + 1;
				}
			} else if(inMLC){ // current position in current line is part of a multiline comment
				firstMLC = findFirst(line, "*/");
				if (firstMLC < 0) { // not closing the MLC, done with this line
					char = size(line);
				} else { // close the MLC
					char = firstMLC + 2;
			 		inMLC = false;
				}
			} else { // current position in current line is not part of a string or multiline comment
				firstSLC = findFirst(line, "//");
				firstMLC = findFirst(line, "/*");
				firstQ = findFirst(line, "\"");
				if (firstSLC < 0 && firstMLC < 0 && firstQ < 0) { // no start of a comment or string found
					char = size(line);
					posdif = size(line);
				} else {
					if (firstSLC != -1 && (firstMLC == -1 || firstSLC < firstMLC) && (firstQ == -1 || firstSLC < firstQ)) { // start of a single-line comment
						char = size(line);
						posdif = firstSLC;
					} else if (firstMLC >= 0 && (firstQ == -1 || firstMLC < firstQ)) { // start of a multi-line comment
						char = firstMLC + 2;
						inMLC = true;
						posdif = firstMLC;
					} else { // start of a string
						char = firstQ + 1;
						inSTR = true;
						posdif = firstQ;
					}
				}
				if(posdif > 0 && /\S/ := substring(line, 0, posdif)) {
					hasCode = true;
				}
			}
		}
		if(hasCode){
			numSLOC += 1;
		}
	}
	return numSLOC;
}

test bool testPCE() 
  = SLOCinFile(|project://jpacman-framework/src/main/java/nl/tudelft/jpacman/PacmanConfigurationException.java|) 
  == 9; //verified by hand

test bool testB() 
  = SLOCinFile(|project://jpacman-framework/src/main/java/nl/tudelft/jpacman/board/Board.java|) 
  == 34; //verified by hand

test bool testGameFolder()
  = sloc(|project://jpacman-framework/src/main/java/nl/tudelft/jpacman/game|)
  == 53 + 15 + 24;
