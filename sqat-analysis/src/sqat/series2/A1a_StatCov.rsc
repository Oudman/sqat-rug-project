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
  A: The system coverage is 41.0%. The list of non-covered methods is kinda long :p
- how do your results compare to the jpacman results in the paper? Has jpacman improved?
  A: Jpacman is not named in the paper, so no comparison can be made.
- use a third-party coverage tool (e.g. Clover) to compare your results to (explain differences)
  A: Clover gives a coverage of 71.6%.
  The correlation between our results and the clover results are weak on class level.
  One possible cause of differences could be that the way clover defines test classes and test methods
  (all files in the test folder) differs from the way our coverage test defines test classes (annotations).
  Another possible cause is the obvious difference between our static analysis and clover's running analysis.

*/

M3 jpacmanM3() = createM3FromEclipseProject(|project://jpacman-framework/src|);

/*
1)	Create a call graph of both production and test code. Make a set of all test classes. Make a set of the remaining non-test classes.
*/

// sets of classes, packages and methods
set[loc] classes(M3 m3) = {x[0] | x <- m3@declarations, x[0].scheme == "java+class"};
set[loc] packages(M3 m3) = {x[0] | x <- m3@declarations, x[0].scheme == "java+package"};
set[loc] methods(M3 m3) = {x[0] | x <- m3@declarations, x[0].scheme == "java+method" || x[0].scheme == "java+constructor"};

// a method is a test method if and only if it has a junit test annotation
set[loc] testMethods(M3 m3) = {x | x <- methods(m3), |java+interface:///org/junit/Test| in m3@annotations[x]};
set[loc] nonTestMethods(M3 m3) = methods(m3) - testMethods(m3);

// set of methods per class or package
set[loc] classMethods(M3 m3, loc class) = { x | x <- m3@containment[class], x.scheme=="java+method" || x.scheme == "java+constructor"};
set[loc] packageMethods(M3 m3, loc package) = { x | x <- m3@containment[package], x.scheme=="java+method" || x.scheme == "java+constructor"};

// a class is a test class if and only if one or more of it's test methods are a test method
//bool isTestClass(M3 m3, loc class) = 0 < size({x | x <- classMethods(m3, class), x in testMethods(m3)});
//set[loc] testClasses(M3 m3) = {x | x <- classes(m3), isTestClass(m3, x)};
set[loc] testClasses(M3 m3) = {x[0] | x <- m3@declarations, x[0].scheme == "java+class", /test/ := x[1].path};
set[loc] nonTestClasses(M3 m3) = classes(m3) - testClasses(m3);

set[loc] enums(M3 m3) = {x[0] | x <- m3@declarations, x[0].scheme == "java+enum"};

rel[loc, str, loc] classDefinesMethod(M3 m3, loc class) = {<class, "DM", method> | method <- classMethods(m3, class)};
rel[loc, str, loc] classesDefineMethod(M3 m3) = {*classDefinesMethod(m3, x) | x <- classes(m3)} + {*classDefinesMethod(m3, x) | x <- enums(m3)};

rel[loc, str, loc] methodCallees(M3 m3, loc method) = {<method, "C", called> | called <- m3@methodInvocation[method]};
rel[loc, str, loc] allMethodCallees(M3 m3) = {*methodCallees(m3, x) | x <- methods(m3)};

rel[loc, str, loc] overloadingCallees(M3 m3) = {<x[1], "OC", x[0]> | x <- m3@methodOverrides};

rel[loc, str, loc] callGraph(M3 m3) = classesDefineMethod(m3) + allMethodCallees(m3) + overloadingCallees(m3);

/*
2)	Collected methods covered by these test classes and store these in a set.
*/

set[loc] traverse(set[loc] covered, rel[loc, str, loc] cg) = {*cg[x]["DM"] | x <- covered} + {*cg[x]["C"] | x <- covered} + {*cg[x]["OC"] | x <- covered};

set[loc] coveredMethods(M3 m3) {
	set[loc] covered = {*classMethods(m3, c) | c <- testClasses(m3)};
	rel[loc, str, loc] cg = callGraph(m3);
	solve (covered) {
		covered = covered + traverse(covered, cg);
	}
	return covered;
}

set[loc] nonCoveredMethods(M3 m3) {
	return methods(m3) - coveredMethods(m3);
}

/*
3)	For each non-test class, count number of defined methods.
*/

/*
4)	Use ratio (covered methods in non-test class X) / (defined methods in X) as the estimation on class level.
	Use class level ratio's to calculate package level ratio's.
	Use package level ratio's to calculate system level ratio's.
*/

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

lrel[real, loc] nonTestClassesCoverage(M3 m3) {
	set[loc] cm = coveredMethods(m3);
	result = [<classCoverage(m3, cm, x), x> | x <- nonTestClasses(m3)];
	return sort(result, bool (<real a, loc _>, <real b, loc _>) { return a > b; });
}

real packageCoverage(M3 m3, set[loc] coveredMethods, loc package) {
	set[loc] cm = packageMethods(m3, package);
	if (size(cm) >0) {
		return size(cm & coveredMethods) / (size(cm) + 0.0);
	} else {
		println("warning: package has no methods:");
		println(class);
		return 1.0;
	}
}

lrel[real, loc] packagesCoverage(M3 m3) {
	set[loc] cm = coveredMethods(m3);
	result = [<packageCoverage(m3, cm, x), x> | x <- packages(m3)];
	return sort(result, bool (<real a, loc _>, <real b, loc _>) { return a > b; });
}

real systemCoverage(M3 m3) {
	if (size(nonTestMethods(m3)) >0) {
		return size(nonTestMethods(m3) & coveredMethods(m3)) / (size(nonTestMethods(m3)) + 0.0);
	} else {
		println("warning: system has no methods");
		return 1.0;
	}
}