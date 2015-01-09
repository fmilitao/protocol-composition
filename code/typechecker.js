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

	const shift = exports.shift;
	const unify = exports.unify;
	const unfold = exports.unfold;
	const unfoldDefinition = exports.unfoldDefinition;
	const substitution = exports.substitution;
	const subtype = exports.subtype;
	const equals = exports.equals;

	// TypeVariables must be upper cased.
	var isTypeVariableName = function(n){
		return n[0] === n[0].toUpperCase();
	}

	//
	// Auxiliary Definitions
	//

	var isProtocol = function( t ){
		switch( t.type ){
			case types.NoneType:
				return true;
			case types.RelyType:
				return true;
			case types.ExistsType:
				return isProtocol( t.inner() );
			case types.AlternativeType:
			case types.IntersectionType:
			case types.StarType: {
				var ts = t.inner();
				for( var i=0; i<ts.length; ++i ){
					if( !isProtocol( ts[i] ) )
						return false;
				}
				return true;
			}
			case types.DefinitionType:
//FIXME: termination not guaranteed
				return isProtocol( unfold(t) );
			default:
				return false;
		}
	}
	
	var locSet = function( t ){
		
		if( isProtocol(t) )
			return new Set(); // empty set

		switch( t.type ){
			case types.NoneType:
				return new Set(); // empty set
			case types.RelyType:
				return locSet( t.rely() );
			
			case types.GuaranteeType:
				return locSet( t.guarantee() );

			case types.AlternativeType:
			case types.IntersectionType:
			case types.StarType: {
				var ts = t.inner();
				var tmp = new Set();

				for( var i=0; i<ts.length; ++i ){
					locSet( ts[i] ).forEach(
						function(x){
							tmp.add(x);
						});
				}
				
				return tmp;
			}

			case types.ExistsType:
			case types.ForallType:{
				var tmp = locSet( t.inner() )
				var id = t.id().name();

				if( !isTypeVariableName( id ) ){
					// then is location variable
					// and we must remove it, if present, from the set
//FIXME wait... this makes no sense to allow?!
					tmp.delete( id );
				}

				return tmp;
			}

			case types.CapabilityType:
				return locSet( t.location() );

			case types.LocationVariable:
				return new Set( [t.name()]) ;

			case types.DefinitionType:
// FIXME termination not gauranteed?! needs to watchout for cycles.
				return locSet( unfold(t) );

			default:
				error( '@locSet: invalid type, got: '+t.type+' '+t );
		}
	}

	var wfProtocol = function( t ){
// FIXME this is a huge mess
// FIXME termination not guaranteed?! needs to watchout for cycles.
		if( !isProtocol(t) )
			return false;

		switch( t.type ){
			case types.NoneType:
				return true; // empty set

			case types.RelyType: {
				var r = locSet( t.rely() );
				var g = locSet( t.guarantee() );

				if( r.size !== g.size )
					return false;

				var tmp = true;
				r.forEach(function(v){
					if( !g.has(v) )
						tmp = false;
				});
				// some missing element
				if( !tmp )
					return false;

				return true; //TODO wfProtocol( t.rely() ) && wfProtocol( t.guarantee() );
			}
			
			case types.GuaranteeType:
				return wfProtocol( t.guarantee() ) && wfProtocol( t.rely() );

			case types.AlternativeType: {
//FIXME needs to check there is a different trigger
				// all must be valid protocols
//FIXME how does this work when there are existentials??
				return true;
			}

			case types.IntersectionType: {
				// all must be valid protocols
				var ts = t.inner();

				for( var i=0; i<ts.length; ++i ){
					if( !wfProtocol( ts[i] ) )
						return false;
				}
				
				return true;
			}

			case types.StarType: {
//FIXME OK for some to not be valid protocols?
				return true;
			}

			case types.ExistsType:
			case types.ForallType:{
				// FIXME problem when defining P * exists q.(A), etc.
				return true;
			}

			case types.DefinitionType:
// FIXME termination not gauranteed?! needs to watchout for cycles.
				return wfProtocol( unfold(t) );

			default:
				error( '@wfProtocol: invalid type, got: '+t.type );
		}
		return true;
	}

	var unifyState = function( state, protocol ){
//		debugger
		if( protocol.type === types.ExistsType ){
			var t = protocol.inner();
			var i = protocol.id();
			var b = protocol.bound();

			t = unifyState( state, t );

			error( t.type === types.RelyType || '@unifyState: invalid unification for '+t );

			var r = t.rely();
			var x = unify( i, r, state );
//FIXME check bound			
			error( x !== null || '@unifyState: invalid unification for '+r+' and '+x );

			t = substitution( t, i, x );
			// there should not be any '0' since we are opening the existential
			t = shift( t, 0, -1 );

			return t;
		}
		return protocol;
	}

	//
	// State-Protocol Split
	//

	var conformanceStateProtocol = function( g, s, p, q ){
		var work = [];
		var visited = [];
		addWork( work, g, s, p, q );
		return checkSPConformance( work, visited );
	}

	// Auxiliary function that adds work by breaking down the
	// protocols and state into smaller, when possible.
	var addWork = function( work, g, s, p, q ){
		// by (cf:Alternative)
		if( s.type === types.AlternativeType ){
			var si = s.inner();
			for( var i=0; i<si.length; ++i )
				addWork( work, g, si[i], p , q );
			return;
		}

		// by (cf:IntersectionL)
		if( p.type === types.IntersectionType ){
			var pi = p.inner();
			for( var i=0; i<pi.length; ++i )
				addWork( work, g, s, pi[i] , q );
			return;
		}

		// by (cf:IntersectionR)
		if( q.type === types.IntersectionType ){
			var qi = q.inner();
			for( var i=0; i<qi.length; ++i )
				addWork( work, g, s, p, qi[i] );
			return;
		}

		// base case
		work.push( { g: g, s: s, p: p, q: q } );
	}

	var checkSPConformance = function( work, visited ){
//debugger
//var i=0;
		while( work.length > 0 ){
			var w = work.pop();

			if( !contains( visited, w ) ){
				var g = w.g;
				var a = w.s;
				var p = w.p;
				var q = w.q;

console.debug( (i++)+' : '+a+' >> '+p+' || '+q );
			
				if( !stepState( work, g, a, p, q, true ) || 
					!stepState( work, g, a, q, p, false ) )
					return false;

				visited.push( w );
			}
		}
		return true;
	}

	var contains = function( visited, w ){
		for( var i in visited ){
			var v = visited[i];
			
			// by equality
			// for now ignore 'g'
			if( equals( v.s, w.s ) &&
				equals( v.p, w.p ) &&
				equals( v.q, w.q ) )
				return true;

/*
			// TODO by subsumption
			if( subtype( w.s, v.s ) &&
				subtype( v.p, w.p ) &&
				subtype( v.q, w.q ) )
				return true;

			// TODO by weakening, careful since bounds must match too?
			// MESSY on how to type check this case.
*/
		}

		return false;
	}

	var stepState = function( work, g, s, p, q, isLeft ){
		s = unfold(s); // I don't like this
		p = unfold(p); // I don't like this
//debugger
		var addW = function( g, s, p ){
			if( isLeft )
				addWork( work, g, s, p, q );
			else
				addWork( work, g, s, q, p );
		};

		// by (step:None)
		if( p.type === types.NoneType ){
			// no need to add work, we already know this configuration steps
			//addWork( work, g, s, p );
			return true;
		}

		// by (step:Recovery)
		if( equals(s,p) ){
			addW( g, NoneType, NoneType );
			return true;
		}

		// by (step:Alternative)
		if( p.type === types.AlternativeType ){
			var ps = p.inner();
			for( var i=0; i<ps.length; ++i ){
				if( stepState( work, g, s, ps[i], q, isLeft ) )
					return true;
			}
			return false;
		}
		
		// attempts to find matching type/location to open existential
		if( p.type === types.ExistsType ){
			// TODO: bound
			// by (step:Open-Type)
			// by (step:Open-Loc)
			var u = unifyState( s, p );
console.debug( p.toString()+' \n>> '+u.toString() );
			// substitute, check bound
			return u !== null && stepState( work, g, s, u, q, isLeft );
		}

		// TODO: by (step:Frame) --- equality is too strong, we need to find the type that is CONTAINED in 's' such that '... * A' (due to framing)

		if( p.type === types.RelyType && equals( p.rely(), s ) ){
			// case analysis on the guarantee type, 'b'
			var b = p.guarantee();

			// by (step:Step)
			if( b.type === types.GuaranteeType ){
				addW( g, b.guarantee(), b.rely() );
				return true;
			}
		
			// by (step:Step-Type)
			// by (step:Step-Loc)
			if( b.type === types.ForallType ){
				// FIXME: how does this affect existing De Bruijn indexes?
				// FIXME: don't type definitions also imply a shift in the indexes? (new bind)
				var i = b.inner();
				var id = b.id();
				var name = id.name();
				var bound = b.bound();

				var gg = g.newScope();

				gg.setType( name, id );
				if( bound !== null )
					gg.setBound( name, bound );

				addW( gg, i.guarantee(), i.rely() );
				return true;
			}

			// assume case is that of omitted '; none' a 'b' is the new state.
			// assume that type was previously checked to be well-formed.
			addW( g, b, NoneType );
			return true;
		}

		return false;
	}

//TODO: Protocol-Protocol Split

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
				var s = subtype(left,right);
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
				var tmp = env.getType( label );
				// if label matches type in environment, but we only allow
				// access to type variables and location variables using this
				// AST.kind --- all other uses are assumed to be recursives.
				if( tmp !== undefined &&
					( tmp.type === types.TypeVariable ||
					  tmp.type === types.LocationVariable ) ){
						return tmp.copy( env.getTypeDepth(label) );
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
							( 'Argument #'+i+' is not LocationVariable: '+tmp.type ), 
							args[i] );
					}
					
					if( t_args[i].type === types.TypeVariable ){
						assert( ( tmp.type !== types.LocationVariable ) ||
							( 'Argument #'+i+' cannot be a LocationVariable' ), 
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

				assert( wfProtocol( left ) || ('Invalid protocol: '+left ) , ast.a );
				assert( wfProtocol( right ) || ('Invalid protocol: '+right ) , ast.b );

				// Protocol conformance, goes through all possible "alias
				// interleaving" and ensure all those possibilities are considered
				// in both protocols.

				var res = conformanceStateProtocol( env, cap, left, right );

				// checkProtocolConformance(cap, left, right, ast);
				
				assert( ast.value === res || ('Unexpected Result, got '+res+' expecting '+ast.value) , ast);
				
				// returns unit
				return new BangType(new RecordType());
			};
			
			// TYPES
			case AST.RELY_TYPE: 
			return function( ast, env ){
				var rely = check( ast.left, env );
				var guarantee = check( ast.right, env );
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
					bound = !ast.bound ? TopType : check( ast.bound, env );
					variable = new TypeVariable( id, 0, bound );
				}
				else{
					variable = new LocationVariable( id, 0 );
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
				var loc = env.getType( id );
				
				assert( (loc !== undefined && loc.type === types.LocationVariable) ||
					('Unknow Location Variable '+id), ast);

				return new CapabilityType( loc.copy( env.getTypeDepth( id ) ), check( ast.type, env ) );
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
		var env = new Environment( null, typedef );
		
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
				var args = typedef.getType(type.id);
				
				// sets the variables, if there are any to setup
				if( args !== null ){
					for(var j=0;j<args.length;++j){
						// should be for both LocationVariables and TypeVariables
						// we must create a new scope to increase the De Bruijn index
						tmp_env = tmp_env.newScope();
						tmp_env.setType( args[j].name(), args[j] );
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
			var info = { ast : ast, env : env.clone() };
			type_info.push( info );

			var res = c( ast, env );
			info.res = res;
			/*
			if( ast.kind === AST.SHARE ){
				info.conformance = hack_info; //FIXME hack_info
			}*/
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

