module sqat::series2::A1a_StatCov

import lang::java::jdt::m3::Core;
import analysis::m3::Core;
import lang::java::m3::Core;
import util::Math;
import Set;
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
- how do your results compare to the jpacman results in the paper? Has jpacman improved?
- use a third-party coverage tool (e.g. Clover) to compare your results to (explain differences)

*/

M3 jpacmanM3() = createM3FromEclipseProject(|project://jpacman-framework/src|);

/*
1)	Create a call graph of both production and test code. Make a set of all test classes. Make a set of the remaining non-test classes.
*/
set[loc] classes(M3 m3) = {x[0] | x <- m3@declarations, x[0].scheme == "java+class"};
set[loc] methods(M3 m3) = {x[0] | x <- m3@declarations, x[0].scheme == "java+method" || x[0].scheme == "java+constructor"};

set[loc] testMethods(M3 m3) = {x | x <- methods(m3), |java+interface:///org/junit/Test| in m3@annotations[x]};

set[loc] classMethods(M3 m3, loc class) = { x | x <- m3@containment[class], x.scheme=="java+method" || x.scheme == "java+constructor"};
bool isTestClass(M3 m3, loc class) = 0 < size({x | x <- classMethods(m3, class), x in testMethods(m3)});

set[loc] testClasses(M3 m3) = {x | x <- classes(m3), isTestClass(m3, x)};
set[loc] nonTestClasses(M3 m3) = classes(m3) - testClasses(m3);

rel[loc, str, loc] classDefinesMethod(M3 m3, loc class) = {<class, "DM", method> | method <- classMethods(m3, class)};
rel[loc, str, loc] classesDefineMethod(M3 m3) = {*classDefinesMethod(m3, x) | x <- classes(m3)};

rel[loc, str, loc] methodCallees(M3 m3, loc method) = {<method, "C", called> | called <- m3@methodInvocation[method]};
rel[loc, str, loc] allMethodCallees(M3 m3) = {*methodCallees(m3, x) | x <- methods(m3)};

rel[loc, str, loc] callGraph(M3 m3) = classesDefineMethod(m3) + allMethodCallees(m3);

/*
2)	Collected methods covered by these test classes and store these in a set.
*/

set[loc] traverse(M3 m3, set[loc] covered) = {*callGraph(m3)[x]["C"] | x <- covered};

set[loc] coveredMethods(M3 m3) {
	set[loc] covered = testMethods(m3);
	solve (covered) {
		covered = covered + traverse(m3, covered);
	}
	return covered;
}

real classCoverage(M3 m3, set[loc] coveredMethods, loc class) {
	set[loc] cm = classMethods(m3, class);
	if (size(cm) >0) {
		return size(cm & coveredMethods) / (size(cm) + 0.0);
	} else {
		println("Warning: class has no methods:");
		println(class);
		return 1.0;
	}
}

rel[loc, real] nonTestClassesCoverage(M3 m3) {
	set[loc] cm = coveredMethods(m3);
	return {<x, classCoverage(m3, cm, x)> | x <- nonTestClasses(m3)};
}


/*
3)	For each non-test class, count number of defined methods.
*/

//{x | x <- tmp@containment[toList(tmp@names["Board"])[1]], x.scheme == "java+method"};

/*
4)	Use ratio (covered methods in non-test class X) / (defined methods in X) as the estimation on class level.
	Use class level ratio's to calculate package level ratio's.
	Use package level ratio's to calculate system level ratio's.
*/









