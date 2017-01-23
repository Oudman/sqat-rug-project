module sqat::series2::A1a_StatCov

import lang::java::jdt::m3::Core;
import analysis::m3::Core;
import lang::java::m3::Core;
import util::Math;
import Set;
import List;
import IO;

/*

Implement static code coverage metrics by Alves & Visser 
(https://www.sig.eu/en/about-sig/publications/static-estimation-test-coverage)


The relevant base data types provided by M3 can be found here:

- module analysis::m3::Core:

rel[loc name, loc src]        M3@declarations;            // maps declarations to where they are declared. contains any kind of data or type or code declaration (classes, fields, methods, variables, etc. etc.)
rel[loc name, TypeSymbol typ] M3@types;                   // assigns types to declared source code artifacts
rel[loc src, loc name]        M3@uses;                    // maps source locations of usages to the respective declarations
rel[loc from, loc to]         M3@containment;             // what is logically contained in what else (not necessarily physically, but usually also)
list[Message]                 M3@messages;                // error messages and warnings produced while constructing a single m3 model
rel[str simpleName, loc qualifiedName]  M3@names;         // convenience mapping from logical names to end-user readable (GUI) names, and vice versa
rel[loc definition, loc comments]       M3@documentation; // comments and javadoc attached to declared things
rel[loc definition, Modifier modifier] M3@modifiers;     // modifiers associated with declared things

- module  lang::java::m3::Core:

rel[loc from, loc to] M3@extends;            // classes extending classes and interfaces extending interfaces
rel[loc from, loc to] M3@implements;         // classes implementing interfaces
rel[loc from, loc to] M3@methodInvocation;   // methods calling each other (including constructors)
rel[loc from, loc to] M3@fieldAccess;        // code using data (like fields)
rel[loc from, loc to] M3@typeDependency;     // using a type literal in some code (types of variables, annotations)
rel[loc from, loc to] M3@methodOverrides;    // which method override which other methods
rel[loc declaration, loc annotation] M3@annotations;

Tips
- encode (labeled) graphs as ternary relations: rel[Node,Label,Node]
- define a data type for node types and edge types (labels)
- use the solve statement to implement your own (custom) transitive closure for reachability.

Questions:
- what methods are not covered at all?
  A: The system coverage is 77.4%. A total number of 53 methods are not covered, these are in the set nonCoveredMethods(jpacmanM3()).
- how do your results compare to the jpacman results in the paper? Has jpacman improved?
  A: The version of jpacman covered in the paper has a static coverage of 84.53%. So no, jpacman has not improved.
- use a third-party coverage tool (e.g. Clover) to compare your results to (explain differences)
  A: Clover gives a system coverage of 71.6%. This is in line with our results. Correlations on 
  Correlations on class level are weak, but there seems to be a correlations between classes having a lot of methods and a strong correlation
  with the clover results. The cause of this is probably the essential difference between static and dynamic test coverage testing, our
  implementation has to guess whether or not an edge in the call graph is or is not reached. On average, guesses are in line with actual graph
  paths, but results may frequently differ in classes with one or just a few methods. Interestingly, this observation is exactly the
  opposite of one of the conclusions of the paper.

Interesting: various Jpacman versions have different results.
The paper used jpacman 3.0.3:
  static: 84.53%; clover: 90.61%
In this presentation jpacman 3.0.4 is used: http://wiki.di.uminho.pt/twiki/pub/Personal/Tiago/Publications/2008-11-27-ipa-testcoverage.pdf 
  static: 88.06%; clover: 93.53%
Our results with jpacman 6.0 (?):
  static: 77.45%; clover: 71.60%

*/

M3 jpacmanM3() = createM3FromEclipseProject(|project://jpacman-framework/src|);

// ------------------------------------------------
// 1a) Sets of packages, classes, enums and methods
// sets of classes, packages and methods
set[loc] packages(M3 m3) = {x[0] | x <- m3@declarations, x[0].scheme == "java+package"};
set[loc] classes(M3 m3) = {x[0] | x <- m3@declarations, x[0].scheme == "java+class"};
set[loc] enums(M3 m3) = {x[0] | x <- m3@declarations, x[0].scheme == "java+enum"};
set[loc] methods(M3 m3) = {x[0] | x <- m3@declarations, x[0].scheme == "java+method" || x[0].scheme == "java+constructor"};

// set of methods per class or package
set[loc] classMethods(M3 m3, loc class) = {x | x <- m3@containment[class], x.scheme=="java+method" || x.scheme == "java+constructor"};

// 1b) Call graph construction
// define method edges
rel[loc, str, loc] classDefinesMethod(M3 m3, loc class) = {<class, "DM", method> | method <- classMethods(m3, class)};
rel[loc, str, loc] classesDefineMethod(M3 m3) = {*classDefinesMethod(m3, x) | x <- classes(m3)} + {*classDefinesMethod(m3, x) | x <- enums(m3)};

// vanilla call edges
rel[loc, str, loc] vanillaCallees(M3 m3) = {<x[0], "C", x[1]> | x <- m3@methodInvocation};

// virtual call edges
set[loc] getConstructors(M3 m3, loc class) = {x | x <- m3@containment[class], x.scheme == "java+constructor"};
bool hasConstructor(M3 m3, loc class) = size(getConstructors(m3, class)) > 0;
loc getConstructor(M3 m3, loc class) = head(sort(getConstructors(m3, class)));
rel[loc, str, loc] virtualCallees(M3 m3) = {<cs, "VC", getConstructor(m3, super)> | <sub, super> <- m3@extends, cs <- getConstructors(m3, sub), super in classes(m3), hasConstructor(m3, super)};

// overloading call edges
rel[loc, str, loc] overloadingCallees(M3 m3) = {<x[1], "OC", x[0]> | x <- m3@methodOverrides};

// call graph
rel[loc, str, loc] callGraph(M3 m3) = classesDefineMethod(m3) + vanillaCallees(m3) + overloadingCallees(m3) + virtualCallees(m3);

// 1c) Sets of test classes and methods
// a class is a test class if and only if 'test' is part of the file path 
set[loc] testClasses(M3 m3) = {x[0] | x <- m3@declarations, x[0].scheme == "java+class", /test/ := x[1].path};
set[loc] nonTestClasses(M3 m3) = classes(m3) - testClasses(m3);

// a method is  test method if and only the method is in a test class
set[loc] testMethods(M3 m3) = {*classMethods(m3, class) | class <- testClasses(m3)};
set[loc] nonTestMethods(M3 m3) = methods(m3) - testMethods(m3);


// -----------------------------------------------------------------------------
// 2) Collect methods covered by these test classes and store these in a set
// set of covered methods
set[loc] traverse(set[loc] covered, rel[loc, str, loc] cg) = {*cg[x]["DM"] | x <- covered} + {*cg[x]["C"] | x <- covered} + {*cg[x]["OC"] | x <- covered} + {*cg[x]["VC"] | x <- covered};
set[loc] coveredMethods(M3 m3) {
	set[loc] covered = {*classMethods(m3, c) | c <- testClasses(m3)};
	rel[loc, str, loc] cg = callGraph(m3);
	solve (covered) {
		covered = covered + traverse(covered, cg);
	}
	return covered;
}

// set of non-covered methods
set[loc] nonCoveredMethods(M3 m3) {
	return methods(m3) - coveredMethods(m3);
}

// -----------------------------------------------------------
// 3) For each non-test class, count number of defined methods
// 4) Use ratio (covered methods in non-test class X) / (defined methods in X) as the estimation on class level. Repeat this on Package and System level.
// class coverage for a given class
real classCoverage(M3 m3, set[loc] coveredMethods, loc class) {
	set[loc] cm = classMethods(m3, class);
	if (size(cm) >0) {
		return size(cm & coveredMethods) / (size(cm) + 0.0);
	} else {
		println("warning: class has no methods:");
		println(class);
		return 1.0;
	}
}

// class coverage for every non-test class
lrel[loc, real] nonTestClassesCoverage(M3 m3) {
	set[loc] cm = coveredMethods(m3);
	result = [<class, classCoverage(m3, cm, class)> | class <- nonTestClasses(m3)];
	return sort(result, bool (<loc a, real _>, <loc b, real _>) { return a < b; });
}

// system coverage
real systemCoverage(M3 m3) {
	if (size(nonTestMethods(m3)) >0) {
		return size(nonTestMethods(m3) & coveredMethods(m3)) / (size(nonTestMethods(m3)) + 0.0);
	} else {
		println("warning: system has no methods");
		return 1.0;
	}
}