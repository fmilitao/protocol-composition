// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

/**
 * INCLUDE parser.js
 * INCLUDE typechecker.types.js
 * INCLUDE typechecker.utils.js
 * 	AST : AST.kinds, for all AST case analysis needs.
 *  TypeChecker : stuff in typechecker.*.js
 */

var TypeChecker = (function( AST, exports ){

	// define constants for convenience
	const assert = exports.assert;
	const error = exports.error;

	const types = exports.types;
	const fct = exports.factory;

	const FunctionType = fct.FunctionType;
	const BangType = fct.BangType;
	const SumType = fct.SumType;
	const StarType = fct.StarType;
	const AlternativeType = fct.AlternativeType;
	const IntersectionType = fct.IntersectionType;
	const ForallType = fct.ForallType;
	const ExistsType = fct.ExistsType;
	const RecordType = fct.RecordType;
	const NoneType = new fct.NoneType();
	const TopType = new fct.TopType();
	const TupleType = fct.TupleType;
	const ReferenceType = fct.ReferenceType;
	const StackedType = fct.StackedType;
	const CapabilityType = fct.CapabilityType;
	const LocationVariable = fct.LocationVariable;
	const TypeVariable = fct.TypeVariable;
	const PrimitiveType = fct.PrimitiveType;
	const RelyType = fct.RelyType;	
	const DefinitionType = fct.DefinitionType;
	const GuaranteeType = fct.GuaranteeType;

	const Gamma = exports.Gamma;
	const TypeDefinition = exports.TypeDefinition;

	const unfold = exports.unfold;
	const substitution = exports.substitution;
	const subtype = exports.subtype;
	const equals = exports.equals;
		
//
// Protocol Conformance
//

/*
 * Extracts the initial state of a protocol, or undefined if it is not a
 * protocol that was given as argument.
 */
var getInitialState = function( p ){
	p = unfold(p);
	switch(p.type){
		case types.RelyType:
			return p.rely();
		case types.AlternativeType:{
			var tmp = new AlternativeType();
			var alts = p.inner();
			for(var i=0;i<alts.length;++i){
				var j = getInitialState(alts[i]);
				if( j === undefined )
					return undefined;
				tmp.add(j);
			}
			return tmp;
		}
		case types.IntersectionType:{
			var tmp = new IntersectionType();
			var v = [];
			var alts = p.inner();
			for(var i=0;i<alts.length;++i){
				var j = getInitialState(alts[i]);
				if( j === undefined )
					return undefined;
				// simplistic way to avoid repeating alternatives
				var found=false;
				for(var u=0;u<v.length;++u){
					if( equals(v[u],j) ){
						found=true;
						break;
					}
				}
				if( !found ){
					tmp.add(j);
					v.push(j);
				}
			}
			if( v.length === 1 )
				return v[0];
			return tmp;
		}
		case types.NoneType:
			return NoneType;
		default:
			// not a valid protocol
			return undefined;
	}
}

/**
 * Protocol Conformance
 */
var checkProtocolConformance = function( s, a, b, ast ){
	var initial = getInitialState(s);
	
	if( initial === undefined ){
		hack_info = conformanceStateProtocol(s,a,b,ast);
	}else{
		hack_info = conformanceProtocolProtocol(initial,s,a,b,ast);
	}
};

	/**
	 * Checks if 'p' accepts 's' with resulting guarantee of 'm'.
	 * @param 's' - initial state
	 * @param 'p' - protocol
	 * @param 'm' - state to match
	 * @return residual protocol of 'p'
	 */
	var simM = function( s, p, m, ast ){
		
		// unfold definition
		p = unfold(p);
		
		if( p.type === types.NoneType ){
			assert( equals( s, m ) ||
				('Mismatch: '+s+' != '+m+', on '+p) , ast );
			return p;
		}

		if( s.type === types.AlternativeType ){
			var tmp_s = null;
			var tmp_p = null;
			var alts = s.inner();

			for( var i=0; i<alts.length; ++i ){
				var tmp = simM( alts[i], p, m, ast );
				if( tmp_s === null ){
					tmp_s = tmp.s;
					tmp_p = tmp.p;
				}else{
					assert( (equals( tmp_s, tmp.s ) && equals( tmp_p, tmp.p )) ||
						('Alternatives mimatch.\n'+
						'(1)\tstate:\t'+tmp_s+'\n\tstep:\t'+tmp_p+'\n'+
						'(2)\tstate:\t'+tmp.s+'\n\tstep:\t'+tmp.p+'\n'), ast );
				}
			}

			return tmp_p;
		}
		
		// attempts alternative that works
		if( p.type === types.AlternativeType ){
			var alts = p.inner();
			for( var i=0; i<alts.length; ++i ){
				try{
					return simM( s, alts[i], m, ast );
				}catch(e){
					continue;
				}
			}
			assert( 'No matching alternative.\n'+
				'state:\t'+s+'\n'+
				'match:\t'+m+'\n'+
				'step:\t'+p, ast );
		}
		
		// only needs one choice that matches
		if( p.type === types.IntersectionType ){
			var alts = p.inner();
			for( var i=0; i<alts.length; ++i ){
				try{
					return simM( s, alts[i], m, ast );
				}catch(e){
					continue;
				}
			}
			assert( '[Protocol Conformance] No matching choice.\n'+
				'state:\t'+s+'\n'+
				'match:\t'+m+'\n'+
				'step:\t'+p, ast );
		}

		// base case
		assert( p.type === types.RelyType ||
			('Expecting RelyType, got: '+p.type+'\n'+pp), ast);
		
		assert( subtype( s, p.rely() ) ||
			('Invalid Step: '+s+' VS '+p.rely()), ast );
		
		var next = p.guarantee();
		assert( next.type === types.GuaranteeType ||
			('Expecting GuaranteeType, got: '+next.type), ast);

		var g = next.guarantee();
		assert( subtype( g, m ) || ('Incompatible: '+g+' vs '+m), ast );
	
		return next.rely();
	}
	
	var mergeAlt = function(a,b){
		if( equals(a,b) )
			return a;
		
		var a_alt = a.type === types.AlternativeType;
		var b_alt = b.type === types.AlternativeType;
		
		var res = new AlternativeType();
		var tmp = ( a_alt ? a.inner() : [a] ).concat( 
				( b_alt ? b.inner() : [b] ) );
		
		for( var i=0; i<tmp.length; ++i ){
			var found = false;
			for( var j=(i+1); j<tmp.length; ++j ){
				if( equals(tmp[i], tmp[j])){
					found = true;
					break;
				}
			}
			if( !found )
				res.add( tmp[i] );
		}
		
		return res;
	}
	
	// generates all possible variantes of 'p' base on subtyping intersections 
	var breakProtocol = function(p){
		// unfold definition
		p = unfold(p);
		//debugger
		if( p.type === types.IntersectionType ){
			return p.inner();
		}
		
		if( p.type === types.AlternativeType ){
			var a = p.inner();
			var tmp = [];
			for( var i=0; i<a.length; ++i ){
				var t = breakProtocol(a[i]);
				if( tmp.length === 0 ){
					tmp = t;
				} else {
					var tmp1 = [];
					// assumed t >= 1
					for( var k=0; k<t.length; ++k ){
						for( var j=0; j<tmp.length; ++j ){
							tmp1.push( [t[k]].concat(tmp[j]) );
						}
					}
					tmp = tmp1;
				}
			}
			
			// each row of tmp includes an alternative type
			var res = [];
			for( var k=0; k<tmp.length; ++k ){
				var t = new AlternativeType();
				for( var j=0; j<tmp[k].length; ++j ){
					var x = tmp[k][j];
					// avoid nesting alternatives inside alternatives (due to 
					// unfolding definitions)
					if( x.type === types.AlternativeType ){
						x = x.inner();
						for( var i=0; i<x.length; ++i )
							t.add( x[i] );	
					}else{
						t.add( x );
					}
				}
				res.push( t );
			}
			
			return res;
		}
		
		// nothing to do.
		return [p];
	}
	
	/**
	 * @param 's' state
	 * @param 'p' protocol
	 * @param 'o' protocol to match with result of moving p with s.
	 * @returns the next state of moving both protocols with 's'.
	 */
	var simP = function( s, p, o, ast ){

		// unfold definitions
		p = unfold(p);

		// unchanged
		if( p.type === types.NoneType ){
			// nothing to be matched
			return { state : s, protocol: p, other: o };
		}

		// now state
		if( s.type === types.AlternativeType ){
			var base = null;
			var alts = s.inner();
//FIXME does none mess this up?
			for( var i=0; i<alts.length; ++i ){
				var tmp = simP( alts[i], p, o, ast );
				if( base === null ){
					base = tmp;
				}else{
					// merge using alternatives
					base.state = mergeAlt( base.state, tmp.state );
					base.protocol = mergeAlt( base.protocol, tmp.protocol );
					base.other = mergeAlt( base.other, tmp.other );
				}
			}
			return { state : base.state, protocol: base.protocol, other: base.other };
		}
		
		// tries to find one alternative that works
		if( p.type === types.AlternativeType ){
			var alts = p.inner();
			for( var i=0; i<alts.length; ++i ){
				try{
					return simP( s, alts[i], o, ast );
				}catch(e){
					// assume it is an assertion error, continue to try with
					// some other alternative
					continue;
				}
			}
			assert( 'No matching alternative on:\n'+
				'state:\t'+s+'\nmatch:\t'+o+'\nprot.:\t'+p, ast );
		}
		
		assert( (p.type !== types.IntersectionType) ||
			('Unsupported protocol format '+p), ast );

		// base case
		assert( p.type === types.RelyType ||
			('Expecting RelyType, got: '+p.type+'\n'+p), ast);

		// ensure A <: B where state is A and protocol B => C		
		assert( subtype( s, p.rely() ) ||
			('Invalid Step: '+s+' VS '+p.rely()), ast );
		
		var next = p.guarantee();
		assert( next.type === types.GuaranteeType ||
			('Expecting GuaranteeType, got: '+next.type), ast);
		
		var m = simM( s, o, next.guarantee(), ast );
		
		return { state: next.guarantee(), protocol: next.rely(), other: m };
	}
	
	/**
	 * Does single step on protocol 'p' with state 's'. Result is an array with
	 * all possible steps that can be taken. Each entry with object to label
	 * the next state as 's' and the residual protocol as 'p'.
	 */
	var step = function(s,p, ast){
		// unfold definitions
		p = unfold(p);
		
		// unchanged
		if( p.type === types.NoneType )
			return [{ state : s , protocol : p }];

		// now state
		if( s.type === types.AlternativeType ){
			var base = null;
			var alts = s.inner();
			for( var i=0; i<alts.length; ++i ){
				var tmp = step(alts[i],p, ast);
				if( base === null ){
					base = tmp[0];
				}
				for( var j=0; j<tmp.length; ++j ){
					assert( (equals( base.state, tmp[j].state ) &&
								equals( base.protocol, tmp[j].protocol )) ||
						('Alternatives mismatch.\n'+
						'(1)\tstate:\t'+base.state+'\n\tstep:\t'+base.protocol+'\n'+
						'(2)\tstate:\t'+tmp[j].state+'\n\tstep:\t'+tmp[j].protocol+'\n'), ast );
				}
			}
			return [{ state : base.state , protocol : base.protocol }];
		}
		
		if( p.type === types.AlternativeType ){
			var alts = p.inner();
			for( var i=0; i<alts.length; ++i ){
				try{
					return step(s,alts[i], ast);
				}catch(e){
					continue; // try with another alternative
				}
			}
			assert( 'No matching alternative:\n'+
				'state:\t'+s+'\n'+'step:\t'+p, ast );
		}
		
		if( p.type === types.IntersectionType ){
			var alts = p.inner();
			var w = [];
			for( var i=0; i<alts.length; ++i ){
				w = w.concat( step(s,alts[i], ast) );
			}
			return w;
		}
		
		assert( p.type === types.RelyType ||
			('Expecting RelyType, got: '+p.type+'\n'+p), ast);
		
		assert( subtype( s, p.rely() ) ||
			('Expecting: '+p.rely()+' got: '+s), ast );
		
		var next = p.guarantee();
		assert( next.type === types.GuaranteeType ||
			('Expecting GuaranteeType, got: '+next.type), ast);
		
		return [{ state : next.guarantee() , protocol : next.rely() }];		
	}

var Visited = function(){
	var visited = [];
	
	this.array = visited;
	
	this.contains = function( state ){
		var s = state[0];
		var p = state[1];
		var a = state[2];
		var b = state[3];
		
		for( var i=0; i<visited.length; ++i ){
			var tmp = visited[i];
// does using subtyping make sense anywhere else?
			if( subtype(s,tmp[0]) &&
					equals(p,tmp[1]) && 
					equals(a,tmp[2]) &&
// intentional: even when b/tmp[3] are left undefined, this is still true.
					equals(b,tmp[3]) )
				return true;
		}
		
		return false;
	};
	
	this.containsS = function( state ){
		var s = state[0];
		var p = state[1];
		var a = state[2];
		var b = state[3];
		
		for( var i=0; i<visited.length; ++i ){
			var tmp = visited[i];
			if( subtype(s,tmp[0]) &&
					subtype(p,tmp[1]) && 
					subtype(a,tmp[2]) &&
					subtype(b,tmp[3]) )
				return true;
		}
		
		return false;
	};
	
	this.push = function( state ){
		visited.push( state );
	};
	
};

var conformanceProtocolProtocol = function( s, p, a, b, ast ){

	var max_visited = 100; // safeguard against 'equals' bugs, bounds execution.	
	var visited = new Visited();
	
	var work = [];
	work.push( [s,p,a,b] ); // initial configuration

	while( work.length > 0 ){
		var state = work.pop();

// this check is slower than pure equals
		if( visited.containsS( state ) )
			continue;

		visited.push( state );

		var S = state[0]; // state
		var P = state[1]; // original protocol
		var A = state[2]; // new protocol
		var B = state[3]; // new protocol
	
		var As = breakProtocol( A );
		for(var j=0;j<As.length;++j ){
			// 1. step on A matched by P
			var l = simP( S, As[j], P, ast );
			work.push( [ l.state, l.other, l.protocol, B ] );
		}

		var Bs = breakProtocol( B );
		//debugger
		for(var j=0;j<Bs.length;++j ){
			// 2. step on B matched by P
			var r = simP( S, Bs[j], P, ast );
			work.push( [ r.state, r.other, A, r.protocol ] );
		}
		
		// 3. step on P matched by either A or B		
		var Ps = breakProtocol( P );
		for( var i=0; i<Ps.length; ++i ){
			var o = null;
			try{
				o = simP( S, Ps[i], A, ast );
				work.push( [ o.state, o.protocol, o.other, B ] );
			}catch(e){
				var o = simP( S, Ps[i], B, ast );
				work.push( [ o.state, o.protocol, A, o.other ] );
			}
		}
	
		// This is useful to safeguard against different JS implementations...
		// more for debug than requirement of the algorhtm.
		assert( max_visited-- > 0 || 'ERROR: MAX VISITED', ast);
	}

	return visited.array;
};




var conformanceStateProtocol = function( s, a, b, ast ){

	var visited = new Visited();
	var max_visited = 100; // safeguard against 'equals' bugs, bounds execution.	
	
	var work = [];
	work.push( [s,a,b] ); // initial configuration

	while( work.length > 0 ){
		var state = work.pop();

		// already done
		if( visited.contains( state ) )
			continue;

		visited.push( state );

		var S = state[0];
		var A = state[1];
		var B = state[2];

		var l = step( S, A, ast);
		for( var i=0; i<l.length; ++i ){
			work.push( [ l[i].state, l[i].protocol, B ] );
		}
			
		var r = step( S, B, ast);
		for( var i=0; i<r.length; ++i ){
			work.push( [ r[i].state, A, r[i].protocol ] );
		}
		
		// This is useful to safeguard against different JS implementations...
		// more for debug than requirement of the algorhtm.
		assert( max_visited-- > 0 || 'ERROR: MAX VISITED', ast);
	}

	return visited.array;
};

	var hack_info;


	// TypeVariables must be upper cased.
	var isTypeVariableName = function(n){
		return n[0] === n[0].toUpperCase();
	}

	/**
	 * @param {AST} ast, tree to check
	 * @param {Environment} env, typing environment at beginning
	 * @return either the type checked for 'ast' or throws a type error with
	 * 	what failed to type check.
	 */
	var setupAST = function( kind, check ) {
		
		switch( kind ) {

			case AST.SUBSTITUTION:
			return function( ast, env ){
				var type = check( ast.type, env );
				var to = check( ast.to, env );
				var from = check( ast.from, env );

				assert( (from.type === types.LocationVariable || from.type === types.TypeVariable)
					|| ("Can only substitute a Type/LocationVariable, got: "+from.type ), ast.from );

				return substitution(type, from, to);
			};

			case AST.SUBTYPE:
			return function( ast, env ){
				var left = check( ast.a, env );
				var right = check( ast.b, env );
				var s = subtype( left, right, env );
				assert( s==ast.value || ('Unexpected Result, got '+s+' expecting '+ast.value), ast );
				return left;
			};

			case AST.EQUALS:
			return function( ast, env ){
				var left = check( ast.a, env );
				var right = check( ast.b, env );
				var s = equals(left,right);
				assert( s==ast.value || ('Unexpected Result, got '+s+' expecting '+ast.value), ast );
				return left;
			};

			case AST.SUM_TYPE: 
			return function( ast, env ){
				var sum = new SumType();
				for( var i=0; i<ast.sums.length; ++i ){
					var tag = ast.sums[i].tag;
					assert( sum.add( tag, check( ast.sums[i].exp, env ) ) ||
							"Duplicated tag: "+tag, ast.sums[i]);
				}
				return sum;
			};
			
			case AST.INTERSECTION_TYPE: 
			return function( ast, env ){
				var alt = new IntersectionType();
				for( var i=0; i<ast.types.length; ++i ){
					alt.add( check( ast.types[i], env ) );
				}
				return alt;
			};
			
			case AST.ALTERNATIVE_TYPE: 
			return function( ast, env ){
				var alt = new AlternativeType();
				for( var i=0; i<ast.types.length; ++i ){
					alt.add( check( ast.types[i], env ) );
				}
				return alt;
			};
			
			case AST.STAR_TYPE: 
			return function( ast, env ){
				var star = new StarType();
				for( var i=0; i<ast.types.length; ++i ){
					star.add( check( ast.types[i], env ) );
				}
				return star;
			};
			
			case AST.NAME_TYPE: 
			return function( ast, env ){
				// the typing environment remains unchanged because all type
				// definitions and type/location variables should not interfere
				var label = ast.text;
				var typedef = env.getTypeDef();
				var tmp = env.getTypeByName( label );
				// if label matches type in environment, but we only allow
				// access to type variables and location variables using this
				// AST.kind --- all other uses are assumed to be recursives.
				if( tmp !== undefined &&
					( tmp.type === types.TypeVariable ||
					  tmp.type === types.LocationVariable ) ){
						return tmp.copy( env.getNameIndex(label) );
				}
				
				// look for type definitions with 0 arguments
				var lookup_args = typedef.getType(label);
				if( lookup_args !== undefined && lookup_args.length === 0 )
					return new DefinitionType( label, [], typedef );
		
				assert( 'Unknown type '+label, ast);
			};
			
			case AST.DEFINITION_TYPE:
			return function( ast, env ){
				var typedef = env.getTypeDef();
				var id = ast.name;
				var args = ast.args;
				var t_args = typedef.getType(id);
				
				assert( t_args !== undefined || ('Unknown typedef: '+id), ast);
				assert( t_args.length === args.length ||
					('Argument number mismatch: '+args.length+' vs '+t_args.length), ast);

				var arguments = new Array(args.length);
				for(var i=0;i<args.length;++i){					
					var tmp = check( args[i], env );

					if( t_args[i].type === types.LocationVariable ){
						assert( ( tmp.type === types.LocationVariable ) ||
							( 'Argument '+i+' is not LocationVariable: '+tmp.type ), 
							args[i] );
					}
					
					if( t_args[i].type === types.TypeVariable ){
						assert( ( tmp.type !== types.LocationVariable ) ||
							( 'Argument '+i+' should not be LocationVariable' ), 
							args[i] );
					}
					
					arguments[i] = tmp;
				}
				
				return new DefinitionType( id, arguments, typedef );
			};
			
			case AST.TAGGED: 
			return function( ast, env ){
				var sum = new SumType();
				var tag = ast.tag;
				var exp = check(ast.exp, env);
				sum.add( tag, exp);
				if( exp.type === types.BangType ){
					sum = new BangType(sum);
				}
				return sum;
			};
			
			case AST.TUPLE_TYPE:
			return function( ast, env ){
				// Note that TUPLE cannot move to the auto-bang block
				// because it may contain pure values that are not in the
				// typing environment and therefore, its type is only bang
				// or not as a consequence of each field's type and not just
				// what it consumes from the environment
				var rec = new TupleType();
				var bang = true;
						
				for(var i=0;i<ast.exp.length;++i){
					var value = check( ast.exp[i], env );
					rec.add(value);
					if( value.type !== types.BangType )
						bang = false;
				}
				
				if( bang )
					rec = new BangType(rec);

				return rec;
			};
			
			case AST.SHARE: 
			return function( ast, env ){
				var cap = check( ast.type, env );
								
				var left = check( ast.a, env );
				var right = check( ast.b, env );
				
// TODO check well formed protocol, only then do conformance.
// TODO: fix conformance first, then do well-formed?

				/* Protocol conformance, goes through all possible "alias
				 * interleaving" and ensure all those possibilities are considered
				 * in both protocols.
				 */
				checkProtocolConformance(cap, left, right, ast);
				
				assert( ast.value || ('Unexpected Result, got '+true+' expecting '+ast.value) , ast);
				// returns unit
				return new BangType(new RecordType());
			};
			
			// TYPES
			case AST.RELY_TYPE: 
			return function( ast, env ){
				var rely = check( ast.left, env );
				var guarantee = check( ast.right, env );
				if( guarantee.type !== types.GuaranteeType &&
					guarantee.type !== types.ForallType ){ // FIXME
					guarantee = new GuaranteeType( guarantee, NoneType );
				}
				return new RelyType( rely, guarantee );
			};
			
			case AST.GUARANTEE_TYPE: 
			return function( ast, env ){
				var guarantee = check( ast.left, env );
				var rely = check( ast.right, env );
				return new GuaranteeType( guarantee, rely );
			};
			
			case AST.REF_TYPE: 
			return function( ast, env ){
				var id = ast.text;
				var loc = env.getTypeByName( id );
				
				assert( (loc !== undefined && loc.type === types.LocationVariable) ||
					('Unknow Location Variable '+id), ast );
				
				return new ReferenceType( loc.copy( env.getNameIndex( id ) ) );
			};
			
			case AST.EXISTS_TYPE:
			case AST.FORALL:
			case AST.FORALL_TYPE: 
			return (function( ctr ){
				return function( ast, env ){
				var id = ast.id;				
				var variable;
				var bound;
				if( isTypeVariableName(id) ){
					variable = new TypeVariable(id,0);
					bound = !ast.bound ? TopType : check( ast.bound, env );
				}
				else{
					variable = new LocationVariable(id,0);
					bound = null;
				}

				var e = env.newScope( id, variable, bound );
				var type = check( ast.exp, e );

				return new ctr( variable, type, bound );
			}; })
			// body is the same, but the CONSTRUCTOR is different:
			( kind === AST.EXISTS_TYPE ? ExistsType : ForallType );
						
			case AST.NONE_TYPE:
			return function( ast, env ){
				return NoneType;
			};

			case AST.TOP_TYPE:
			return function( ast, env ){
				return TopType;
			};
				
			case AST.BANG_TYPE:
			return function( ast, env ){
				return new BangType( check( ast.type , env ) );
			};
			
			case AST.FUN_TYPE: 
			return function( ast, env ){
				return new FunctionType( 
					check( ast.arg, env ),
					check( ast.exp, env )
				);
			};
			
			case AST.CAP_TYPE: 
			return function( ast, env ){
				var id = ast.id;
				var loc = env.getTypeByName( id );
				
				assert( (loc !== undefined && loc.type === types.LocationVariable) ||
					('Unknow Location Variable '+id), ast);

				return new CapabilityType( loc.copy( env.getNameIndex( id ) ), check( ast.type, env ) );
			};
			
			case AST.STACKED_TYPE: 
			return function( ast, env ){
				return new StackedType(
					check( ast.left, env ),
					check( ast.right, env )
				);
			};
			
			case AST.RECORD_TYPE: 
			return function( ast, env ){
				var rec = new RecordType();
				for( var i=0; i<ast.exp.length ; ++i ){
					var field = ast.exp[i];
					var id = field.id;
					var value = check( field.exp, env );
					assert( rec.add(id, value) ||
						("Duplicated field '" + id + "' in '"+rec+"'"), field);
				}
				return rec;
			};
			
			case AST.PRIMITIVE_TYPE:
			return function( ast, env ){
				// relying on the parser to limit primitive types to ints, etc.
				return new PrimitiveType(ast.text);
			};

			default: // unexpected AST kinds
			return function( ast, env ){
				error( "Not expecting " + ast.kind );
			};
		}

	}
	
	var checkProgram = function( ast, check ){
		// pre: ast is program's root
		error( (ast.kind === AST.PROGRAM) || 'Unexpected AST node' );
				
		var typedef = new TypeDefinition();
		var env = new Gamma( typedef, null );
		
		// handle type definitions
		if( ast.typedefs !== null ){

			// 1st pass: extract all argument definitions, note that
			// duplication is not checked at this stage
			for(var i=0;i<ast.typedefs.length;++i){
				var it = ast.typedefs[i];
				var args = [];
				var pars = it.pars;

				// only do this if there are any actual definition parameters
				if( pars !== null ){
					args = new Array(pars.length);
					
					for(var j=0;j<pars.length;++j){
						var n = pars[j];
						args[j] = isTypeVariableName(n) ? 
							new TypeVariable(n,0) : new LocationVariable(n,0);
					}
				}
				
				assert( typedef.addType(it.id,args) 
					|| ('Duplicated typedef: '+it.id), it );
			}
			
			// 2nd pass: check that any recursion is well-formed (i.e. correct number and kind of argument)
			for(var i=0;i<ast.typedefs.length;++i){
				var type = ast.typedefs[i];						
				var tmp_env = env;
				var args = typedef.getType( type.id );
				
				// sets the variables, if there are any to setup
				if( args !== null ){
					for(var j=0;j<args.length;++j){
						// should be for both LocationVariables and TypeVariables
						tmp_env = tmp_env.newScope( args[j].name(), args[j], null );
					}
				}
				
				// map of type names to typechecker types
				assert( typedef.addDefinition(type.id, check(type.type, tmp_env)) 
					|| ('Duplicated typedef: '+type.id), type );
			}

			// 3rd pass: check for bottom types.
			for(var i=0;i<ast.typedefs.length;++i){
				var type = ast.typedefs[i];
				var x = typedef.getDefinition(type.id);
				var set = new Set();
				while( x.type === types.DefinitionType ){
					// note that we use the string-indexOnly representation of the type
					set.add( x.toString(false) );
					x = unfoldDefinition(x);
					// if already seen this unfold, then type is a cycle
					assert( !set.has( x.toString(false) )
						|| ('Infinite typedef (i.e. bottom type): '+type.id), type );
				}

			}

		}

		// check main expression:
		var exps = ast.exp;
		for( var i=0; i<exps.length; ++i ){
			check( exps[i], env );
		}

		// bogus return... but anyway.
		return NoneType;
	}

	// monad like
	// inspector( ast, env, checkFunction )
	var buildChecker = function( inspector ){
		var map = new Map();
		var aux = function( ast, env ){
			if( !map.has( ast.kind ) )
				error( 'Error @buildChecker Not expecting '+ast.kind );
			return map.get(ast.kind)( ast, env );
		};

		var tmp = aux;
		if( inspector ){
			tmp = function( ast, env ){
				return inspector( ast, env, aux );
			};
		}

		for( var i in AST ){
			error( !map.has(i) || ( 'Error @buildChecker, duplication: '+i ) );
			// find function to call on this kind of AST node
			map.set( i, setupAST( i, tmp ) );
		}

		return tmp;
	};

	// this moved here just to avoid re building checker on each 'check'
	// all these variable could be local variables of 'exports.check'
	var type_info = [];
	var inspector = function( ast, env, c ){
			var info = { ast : ast, env : env };
			type_info.push( info );
			
			var res = c( ast, env );
			
			info.res = res;
			if( ast.kind === AST.SHARE ){
				info.conformance = hack_info; //FIXME hack_info
			}
			return res;
		};
	var checker = buildChecker( inspector );

	// only exports checking function.
	exports.check = function( ast, log ){
		
		type_info = []; // reset

		// timer start
		var start = new Date().getTime();
		
		try{
			return checkProgram( ast, checker );
		} finally {
			if( log ){
				log.diff = (new Date().getTime())-start;
				log.info = type_info; 
			}
		}

	};

	return exports;
	
})( AST.kinds, TypeChecker ); // required globals

