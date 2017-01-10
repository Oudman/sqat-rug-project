module sqat::series1::A3_CheckStyle

import Java17ish;
import ParseTree;
import util::FileSystem;
import Message;
import IO;
import Set;

/*

Assignment: detect style violations in Java source code.
Select 3 checks out of this list:  http://checkstyle.sourceforge.net/checks.html
Compute a set[Message] (see module Message) containing 
check-style-warnings + location of  the offending source fragment. 

Plus: invent your own style violation or code smell and write a checker.

Note: since concrete matching in Rascal is "modulo Layout", you cannot
do checks of layout or comments (or, at least, this will be very hard).

JPacman has a list of enabled checks in checkstyle.xml.
If you're checking for those, introduce them first to see your implementation
finds them.

Questions
- for each violation: look at the code and describe what is going on? 
  Is it a "valid" violation, or a false positive?
  A: No violations were found.

Tips 

- use the grammar in lang::java::\syntax::Java15 to parse source files
  (using parse(#start[CompilationUnit], aLoc), in ParseTree)
  now you can use concrete syntax matching (as in Series 0)

- alternatively: some checks can be based on the M3 ASTs.

- use the functionality defined in util::ResourceMarkers to decorate Java 
  source editors with line decorations to indicate the smell/style violation
  (e.g., addMessageMarkers(set[Message]))

  
Bonus:
- write simple "refactorings" to fix one or more classes of violations 

*/



/* returns set of star import violations including locations, according to http://checkstyle.sourceforge.net/config_imports.html#AvoidStarImport */
set[Message] checkStarImport(loc file) 
	= {info("Star import", imp@\loc) | /ImportDec imp := parse(#start[CompilationUnit], file), /\*/ := readFileLines(imp@\loc)[0]}; // /^import .+\.\*;$/ := imp)};

/* returns set of static import violations including locations, according to http://checkstyle.sourceforge.net/config_imports.html#AvoidStaticImport */
set[Message] checkStaticImport(loc file)
	= {info("Static import", imp@\loc) | /ImportDec imp := parse(#start[CompilationUnit], file), /import\s*static/ := readFileLines(imp@\loc)[0]};

/* returns Message if the the file is too long, according to http://checkstyle.sourceforge.net/config_sizes.html#FileLength */
set[Message] checkFileLength(loc file, int maxLength = 1500) {
	int actualLength = size(readFileLines(file));
	if (actualLength > maxLength) {
		return {info("Large file: <actualLength> LOC", file)}; // file too long
	} else {
		return {};
	}
}

set[Message] checkStyle(loc project) {
	result = {*checkStarImport(f) | /file(f) <- crawl(project), f.extension == "java"};
	result += {*checkStaticImport(f) | /file(f) <- crawl(project), f.extension == "java"};
	result += {*checkFileLength(f) | /file(f) <- crawl(project), f.extension == "java"};
	return result;
}

test bool testA3stars()
  = size(checkStarImport(|project://sqat-analysis/src/sqat/series1/A3_test.java|))
  == 2;

test bool testA3static()
  = size(checkStaticImport(|project://sqat-analysis/src/sqat/series1/A3_test.java|))
  == 2;

test bool testA3size()
  = size(checkFileLength(|project://sqat-analysis/src/sqat/series1/A3_test.java|))
  == 0;

test bool testA3sizeLowThreshold()
  = size(checkFileLength(|project://sqat-analysis/src/sqat/series1/A3_test.java|, maxLength = 150))
  == 1;
