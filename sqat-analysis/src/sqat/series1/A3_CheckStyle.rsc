module sqat::series1::A3_CheckStyle

import lang::java::\syntax::Java15;
import ParseTree;
import util::FileSystem;
import Message;
import IO;

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

set[Message] checkStyle(loc project) {
	result = {*checkStarImport(f) | /file(f) <- crawl(project), f.extension == "java"};
	result += {*checkStaticImport(f) | /file(f) <- crawl(project), f.extension == "java"};
	result += {*checkFileLength(f) | /file(f) <- crawl(project), f.extension == "java"};
	return result;
}

/* returns set of star import violations including locations, according to http://checkstyle.sourceforge.net/config_imports.html#AvoidStarImport */
set[Message] checkStarImport(loc file) 
	= {info("Star import", imp@\loc) | /ImportDec imp := parse(#start[CompilationUnit], file, /^import .+\.\*;$/ == imp)};

/* returns set of static import violations including locations, according to http://checkstyle.sourceforge.net/config_imports.html#AvoidStaticImport */
set[Message] checkStaticImport(loc file)
	= {info("Static import", imp@\loc) | /ImportDec imp := parse(#start[CompilationUnit], file, /^import static .*;$/ == imp)};

/* returns Message if the the file is too long, according to http://checkstyle.sourceforge.net/config_sizes.html#FileLength */
set[Message] checkFileLength(loc file) {
	int maxLength = 15;
	int actualLength = size(readFileLines(file)); // moet vast efficienter kunnen, dit is een vrij lelijke implementatie
	if (actualLength > maxLength) {
		return {info("Large file: <actualLength> LOC", file)}; // file too long
	} else {
		return {};
	}
}

