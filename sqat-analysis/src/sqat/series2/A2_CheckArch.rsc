module sqat::series2::A2_CheckArch

import sqat::series2::Dicto;
import lang::java::jdt::m3::Core;
import Message;
import ParseTree;
import IO;
import Set;
import String;

/*

This assignment has two parts:
- write a dicto file (see example.dicto for an example)
  containing 3 or more architectural rules for Pacman
  
- write an evaluator for the Dicto language that checks for
  violations of these rules. 

Part 1  

An example is: ensure that the game logic component does not 
depend on the GUI subsystem. Another example could relate to
the proper use of factories.   

Make sure that at least one of them is violated (perhaps by
first introducing the violation).

Explain why your rule encodes "good" design.
  
Part 2:  
 
Complete the body of this function to check a Dicto rule
against the information on the M3 model (which will come
from the pacman project). 

A simple way to get started is to pattern match on variants
of the rules, like so:

switch (rule) {
  case (Rule)`<Entity e1> cannot depend <Entity e2>`: ...
  case (Rule)`<Entity e1> must invoke <Entity e2>`: ...
  ....
}

Implement each specific check for each case in a separate function.
If there's a violation, produce an error in the `msgs` set.  
Later on you can factor out commonality between rules if needed.

The messages you produce will be automatically marked in the Java
file editors of Eclipse (see Plugin.rsc for how it works).

Tip:
- for info on M3 see series2/A1a_StatCov.rsc.

Questions
- how would you test your evaluator of Dicto rules? (sketch a design)

- come up with 3 rule types that are not currently supported by this version
  of Dicto (and explain why you'd need them).
  
  	The Dicto language as defined here does not support multiple identifiers on the right-hand side, which makes the "can only" modality less useful. 
  	You would want to be able to specify a list of packages that a package is allowed to import.
  	
  	It also doesn't support "only <Entity e1> can" modality, which would be useful to restrict usage of a certain module to a specific module (or list of modules!).
  	
  	Finally, "<Entity e1> <Modality m> implement <Entity e2>" would be useful for interfaces. An interface is sort of like a contract that a class adheres to, 
  	and enforcing properties through these "contracts" is something you would want to validate on the architectural level.  	
  	
*/


M3 jpacmanM3() = createM3FromEclipseProject(|project://jpacman-framework/src|);

set[loc] packageFiles(loc package, M3 m3) = {f | f <- m3@containment[package], f.scheme=="java+compilationUnit"}
										  + {*packageFiles(p, m3) | p <- m3@containment[package], p.scheme=="java+package"};
										  
set[loc] fileImports(loc file, M3 m3){
	set[str] imports =  {id | line <- readFileLines(file), /\s*import\s*(static)?\s*<id:([A-Za-z_][A-Za-z_0-9]*\.)+([A-Za-z_][A-Za-z_0-9]*|\*)>;/ := line};
	set[loc] importLocs = {};
	
	for(imp <- imports){
		str path = /\*/ := imp ? replaceAll(imp[..-2],".","/") : replaceAll(imp,".","/");
		
		if(locInModel((|java+class:///| + path), m3)){
			importLocs = importLocs + (|java+class:///| + path);
		} else {
			importLocs = importLocs + (|java+package:///| + path);
		}
	}
	
	return importLocs;
}


set[loc] packageImports(loc package, M3 m3){
	set[loc] files = packageFiles(package, m3);
	
	return {*fileImports(x, m3) | x <- files};
}

bool checkModality(loc target, Modality modality, set[loc] invoked) {
	if(modality == (Modality)`must`) {
		return (target in invoked);
	} else if (modality == (Modality)`may`) {
		return true; //Cannot be violated: either it does invoke it, which it is allowed to, or it doesn't, which it doesn't have to.
	} else if (modality == (Modality)`cannot`) {
		return (target notin invoked);
	} else if (modality == (Modality)`can only`) {
		return (false notin {target in {x} + superPackages(x) | x <- invoked});
	} else {
		throw ("\"" + m + "\" is not a valid modality (must|may|cannot|can only)");
	}
}

set[loc] superPackages(loc package) {
	list[str] s = split("/",package.path);
	return {|java+package:///| + intercalate("/",s[1..n]) | int n <- [2..size(s)]};	
}

set[Message] checkImport(Rule r, Entity e1, Entity e2, Modality modality, M3 m3) {
//Check if package e1 imports pkg/class e2

	loc entity1 = |java+package:///| + replaceAll(unparse(e1),".","/");
	loc entity2Package = |java+package:///| + replaceAll(unparse(e2),".","/");
	loc entity2Class = |java+class:///| + replaceAll(unparse(e2),".","/");
	loc en2;
	
	if(!packageExists(entity1,m3)) {
		throw (unparse(e1) + " does not name a valid package.");
	}
	
	if(packageExists(entity2Package,m3)) {
		en2 = entity2Package;
	} else if (locInModel(entity2Class,m3)) {
		en2 = entity2Class;
	} else {
		throw (unparse(e2) + " does not name a valid package/class.");
	}
		
	set[loc] imports = packageImports(entity1,m3);
	
	if (checkModality(en2, modality, imports)) {
	 	return {};
	} else {
	 	return {info("Rule Violation: " + unparse(r), entity1)};
	}
}

set[loc] fileClasses(loc cu, M3 m) = { c | c <- m@containment[cu], cu.scheme == "java+class"};

set[loc] packageClasses(loc p, M3 m) =	{*fileClasses(cu, m) | cu <- packageFiles(p, m)};

bool packageExists(loc p, M3 m) = p in m@names.qualifiedName;

set[Message] checkDepend(Rule r, Entity e1, Entity e2, Modality modality, M3 m3){
	loc entity1Class = |java+class:///| + replaceAll(unparse(e1),".","/");
	loc entity1Package = |java+package:///| + replaceAll(unparse(e1),".","/");
	
	set[loc] dependencies = {};
	loc e;
	
	if ( locInModel(entity1Class, m3) ){
		e = entity1Class;
		
		dependencies = {*superPackages(x) | x <- m3@typeDependency[e]};
	} else if ( packageExists(entity1Package, m3) ) {
		e = entity1Package;
	
		dependencies = {*m@typeDependency[c] | c <- packageClasses(e, m3)};
		
		dependencies = dependencies + {*superPackages(x) | x <- dependencies};
	} else {
		throw (unparse(e1) + " does not name a valid and unique method or constructor.");
	}
	
	loc entity2Class = |java+class:///| + replaceAll(unparse(e1),".","/");
	loc entity2Package = |java+package:///| + replaceAll(unparse(e1),".","/");
	
	if ( locInModel(entity2Class, m3) ){
		return checkModality(entity2Class, modality, dependencies) 
			? {} 
			: {info("Rule Violation: " + unparse(r), e)};
		
	} else if ( packageExists(entity2Package,m3) ) {
		return checkModality(entity2Package, modality, dependencies) 
			? {} 
			: {info("Rule Violation: " + unparse(r), e)};
	} else {
		throw (unparse(e2) + "\" does not name a valid and unique method or constructor.");
	}
	

}

bool locInModel(loc l, M3 m3){
	return l in {stripMethod(x) | x <- m3@names.qualifiedName};
}

loc stripMethod(loc m){
	str last = split("/",m.path)[-1];
	last = split("(",last)[0];
	m.path = intercalate("/",split("/",m.path)[..-1] + "/" + last);
	
	return m;
}

set[Message] checkInvoke(Rule r, Entity e1, Entity e2, Modality modality, M3 m3){
	//Check if e1 calls the method e2
	//e1 and e2 can be either a class or a method
	
	//e1 is either a Method, Constructor or a Class, so we search the declarations for them
	loc entity1Class = |java+class:///| + replaceAll(unparse(e1),".","/");
	loc entity1Method = |java+method:///| + split("(",replaceAll(unparse(e1),".","/"))[0];
	loc entity1Constructor = |java+constructor:///| + replaceAll(unparse(e1),".","/");
	loc en1;
	
	set[loc] invoked = {};
	
	if( locInModel(entity1Class, m3) ){
		en1 = entity1Class;
		invoked = invoked + {*m3@methodInvocation[e] | e <- m3@containment[en1], e.scheme in ["java+method","java.constructor"]};
		
	} else if ( locInModel(entity1Method, m3) ){
		en1 = entity1Method;
		invoked = invoked + m3@methodInvocation[en1];
		
	} else if ( locInModel(entity1Constructor, m3) ){
		en1 = entity1Constructor;
		invoked = invoked + m3@methodInvocation[en1];
		
	} else {
		throw ("\""+ unparse(e1) + "\" does not name a valid and unique class, method or constructor.");
	}
	
	invoked = {stripMethod(x) | x <- invoked};
	
	loc entity2Method = |java+method:///| + replaceAll(unparse(e2),".","/");
	loc entity2Constructor = |java+constructor:///| + replaceAll(unparse(e2),".","/");
	
	if( locInModel(entity2Method, m3) ){
		return checkModality(entity2Method, modality, invoked) 
			? {} 
			: {info("Rule Violation: " + unparse(r), en1)};
	} else if (locInModel(entity2Constructor, m3)){
		return checkModality(entity2Constructor, modality, invoked) 
			? {} 
			: {info("Rule Violation: " + unparse(r), en1)};
	} else {
		throw ("\""+ unparse(e2) + "\" does not name a valid and unique method or constructor.");
	}
	

}

set[loc] methodInstantiates(loc m, M3 m3){
	 set[loc] a = { c | c <- m3@methodInvocation[m], c.scheme == "java+constructor"};
	 
	 return {|java+class:///| + intercalate("/",split("/",c.path)[..-1]) | c <- a};
	 
	 }

set[loc] qualifiedNames(M3 m3) = m3@names.qualifiedName;

set[Message] checkInstantiate(Rule r, Entity e1, Entity e2, Modality modality, M3 m3){
	//Check if method/class/constructor e1 calls a constructor of the class e2
	
	loc entity1Class = |java+class:///| + replaceAll(unparse(e1),".","/");
	loc entity1Method = |java+method:///| + replaceAll(unparse(e1),".","/");
	loc e;
	
	set[loc] invoked = {};
	
	if( locInModel(entity1Class, m3) ){
		e = entity1Class;
		invoked = invoked + {*methodInstantiates(a, m3) | a <- m3@containment[entity1Class], a.scheme in ["java+method","java+constructor"]};
		
	} else if ( locInModel(entity1Method, m3) ){
		e = entity1Method;
		invoked = invoked + methodInstantiates(entity1Method, m3);
		
	} else {
		throw (unparse(e1) + " does not name a valid and unique class or method.");
	}
	
	loc entity2Class = |java+class:///| + replaceAll(unparse(e2),".","/");
	
	if(locInModel(entity2Class, m3)){
		return checkModality(entity2Class, modality, invoked) 
			? {} 
			: {info("Rule Violation: " + unparse(r), e)};
	
	} else {
		throw (unparse(e2) + " does not name a valid and unique class.");
	}

}

set[Message] checkInherit(Rule r, Entity e1, Entity e2, Modality modality, M3 m3){
	//Check if class e1 is a subtype of class e2
	
	loc entity1Class = |java+class:///| + replaceAll(unparse(e1),".","/");
	loc entity2Class = |java+class:///| + replaceAll(unparse(e2),".","/");
	
	set[loc] superClasses = {};
	
	if(locInModel(entity1Class,m3)){
		superClasses = superClasses + m3@extends[entity1Class];
		
	} else {
		throw ("\""+ unparse(e1) + "\" does not name a valid and unique class.");
	}
	
	if(locInModel(entity2Class,m3)){
		return checkModality(entity2Class, modality, superClasses) 
			? {} 
			: {info("Rule Violation: " + unparse(r), entity2Class)};
	} else {
		throw (""+ unparse(e2) + " does not name a valid and unique class.");
	}

}


set[Message] eval(start[Dicto] dicto, M3 m3) = eval(dicto.top, m3);

set[Message] eval((Dicto)`<Rule* rules>`, M3 m3) 
  = ( {} | it + eval(r, m3) | r <- rules );
  
set[Message] eval(Rule rule, M3 m3) {
  set[Message] msgs = {};
  
  // to be done
  switch(rule){
  	case (Rule)`<Entity e1> <Modality m> import <Entity e2>`: 
  		msgs = msgs + checkImport(rule,e1,e2,m,m3);
  	case (Rule)`<Entity e1> <Modality m> depend <Entity e2>`: 
  		msgs = msgs + checkDepend(rule,e1,e2,m,m3);
  	case (Rule)`<Entity e1> <Modality m> invoke <Entity e2>`: 
  		msgs = msgs + checkInvoke(rule,e1,e2,m,m3);
  	case (Rule)`<Entity e1> <Modality m> instantiate <Entity e2>`: 
  		msgs = msgs + checkInstantiate(rule,e1,e2,m,m3);
  	case (Rule)`<Entity e1> <Modality m> inherit <Entity e2>`: 
  		msgs = msgs + checkInherit(rule,e1,e2,m,m3);
  }
  
  return msgs;
}

test bool mustImport(){
	return size(eval((Rule)`nl.tudelft.jpacman.ui must import java.awt.Color`,jpacmanM3())) == 0;
}

test bool cannotDepend(){
	return size(eval((Rule)`nl.tudelft.jpacman.board.Board cannot depend nl.java.tudelft.jpacman.ui`,jpacmanM3())) == 0;
}

test bool mustDepend(){
	set[Message] m = eval((Rule)`nl.tudelft.jpacman.board must depend nl.java.tudelft.jpacman.ui`, jpacmanM3());
	return (size(m) == 1 && getOneFrom(m).msg == "Rule Violation: nl.tudelft.jpacman.board must depend nl.java.tudelft.jpacman.ui");
}

test bool mustInstantiate(){
	return size(eval((Rule)`nl.tudelft.jpacman.level.Level must instantiate java.util.ArrayList`,jpacmanM3())) == 0;
}

test bool canonlyInstantiate(){
	return size(eval((Rule)`nl.tudelft.jpacman.level.Level must instantiate java.util.ArrayList`,jpacmanM3())) == 0;
}

test bool mustInvoke(){
	return size(eval((Rule)`nl.tudelft.jpacman.board.Board must invoke nl.tudelft.jpacman.board.Board.withinBorders`,jpacmanM3())) == 0;
}

test bool mustInherit(){
	return size(eval((Rule)`nl.tudelft.jpacman.level.Pellet must inherit nl.tudelft.jpacman.board.Unit`,jpacmanM3())) == 0;
}

test bool testSuperPackages(){
	return superPackages(|java+constructor:///java/util/ArrayList|) == {|java+package:///java/util|,|java+package:///java|};
}
