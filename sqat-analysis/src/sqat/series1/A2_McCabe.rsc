module sqat::series1::A2_McCabe

import lang::java::\syntax::Java15;
import lang::java::jdt::m3::AST;
import IO;
import Set;
import List;

/*

Construct a distribution of method cylcomatic complexity. 
(that is: a map[int, int] where the key is the McCabe complexity, and the value the frequency it occurs)


Questions:
- which method has the highest complexity (use the @src annotation to get a method's location)

- how does pacman fare w.r.t. the SIG maintainability McCabe thresholds?

	The highest cyclomatic complexity found in jpacman methods is 8, meaning that all methods are classified as "simple" in the SIG model.
	Therefore, the project is rated ++ on complexity per unit.
	
- is code size correlated with McCabe in this case (use functions in analysis::statistics::Correlation to find out)? 
  (Background: Davy Landman, Alexander Serebrenik, Eric Bouwers and Jurgen J. Vinju. Empirical analysis 
  of the relationship between CC and SLOC in a large corpus of Java methods 
  and C functions Journal of Software: Evolution and Process. 2016. 
  http://homepages.cwi.nl/~jurgenv/papers/JSEP-2015.pdf)
  
- what if you separate out the test sources?

Tips: 
- the AST data type can be found in module lang::java::m3::AST
- use visit to quickly find methods in Declaration ASTs
- compute McCabe by matching on AST nodes

Sanity checks
- write tests to check your implementation of McCabe

Bonus
- write visualization using vis::Figure and vis::Render to render a histogram.

*/

set[Declaration] jpacmanASTs() = createAstsFromEclipseProject(|project://jpacman-framework|, true);
set[Declaration] jpacmanSrcASTs() = createAstsFromDirectory(|project://sqat-rug-project/jpacman/src|, true);

alias CC = rel[loc method, int cc];

CC cc(set[Declaration] decls) {
  CC result = {};
  
  for( file <- decls){
    visit(file){
      case meth: \method(_,_,_,_,_): result = result + complexity(meth);
    }
  }
  
  return result;
}

tuple[loc method, int cc] complexity(Declaration method){
	int cc = 1;
	visit(method){
		case \if(_,_) : cc += 1;
		case \if(_,_,_) : cc += 1;
		case \do(_,_) : cc += 1;
		case \for(_,_,_) : cc += 1;
		case \for(_,_,_,_) : cc += 1;
		case foreach(_,_,_) : cc += 1;
		case \while(_,_) : cc += 1;
		case \case(_) : cc += 1;
		//Cases we missed but which were covered by the paper mentioned above:
		case \catch(_,_): cc += 1;
		case \conditional(_,_,_): cc += 1;
		case infix(_,"&&",_) : cc += 1;
		case infix(_,"||",_) : cc += 1;
		
    }
	
	return <method@src, cc>;
}

alias CCDist = map[int cc, int freq];

CCDist ccDist(CC cc) {
  CCDist dist =();
  
  for ( tuple[loc method, int cc] decl <- cc){
    if(decl.cc notin dist){
    	dist = dist + (decl.cc:1);
    } else {
    	dist = dist + (decl.cc : dist[decl.cc] + 1);
    }
  }
  
  return dist;
}

tuple[loc method, int cc] highestComplexity(set[Declaration] decls){
	list[tuple[loc,int]] methods = toList(cc(decls));
	return sort(methods, bool (< loc _, int a>, < loc _, int b>) { return a > b; })[0];
}

num complexitySizeCorrelation(set[Declaration] decls){	
	lrel[int cc, int size] result = [];
	
	for(tuple[loc,int] tup <- cc(decls)){
		result = result + <tup[1], tup[0].end.line - tup[0].begin.line + 1>;
	}
	
	return PearsonsCorrelation(result);

}

test bool launcherCC(){
	Declaration launcherAST = createAstFromFile(|project://sqat-rug-project/jpacman/src/main/java/nl/tudelft/jpacman/Launcher.java|, true);
	
	CC result = cc({launcherAST});
	
	if (size(result) != 21){
		return false;
	}
	
	if (highestComplexity({launcherAST}).cc != 2){
		return false;
	}
	
	CCDist dist = ccDist(result);
	
	if (dist[1] == 19 && dist[2] == 2){
		return true;
	}
	
}
