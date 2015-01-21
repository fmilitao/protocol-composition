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

	const UnitType = new BangType(new RecordType());
	const NoneType = new fct.NoneType();
	const TopType = new fct.TopType();

	const Gamma = exports.Gamma;
	const TypeDefinition = exports.TypeDefinition;

	const shift = exports.shift;
	const unify = exports.unify;
	const unfold = exports.unfold;
	const unfoldDefinition = exports.unfoldDefinition;
	const substitution = exports.substitution;
	const subtype = exports.subtype;
	const equals = exports.equals;
	const isFree = exports.isFree;
	const isProtocol = exports.isProtocol;


	//
	// Auxiliary Definitions
	//

	// TypeVariables must start upper cased.
	var isTypeVariableName = function(n){
		return n[0] === n[0].toUpperCase();
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

		if( protocol.type === types.ExistsType ){
			var t = protocol.inner();
			var i = protocol.id();
			var b = protocol.bound();

			t = unifyState( state, t );

			error( t.type === types.RelyType || '@unifyState: invalid unification for '+t );

			var r = t.rely();
//FIXME: --- this looks ugly needs good justification.
			state = shift( state, 0, 1 );
			var x = unify( i, r, state );
//FIXME check bound			
			error( x !== false || '@unifyState: invalid unification for '+r+' and '+state );

			// if contains valid type.
			if( x !== true ){
				// shift because it is going inside the existential
				x = shift( x, 0, 1 );
				t = substitution( t, i, x );
				// unshift because we are opening the existential
				t = shift( t, 0, -1 );
			}

			return t;
		}
		return protocol;
	}

	// i.e. weakening rule, but going upwards ("strengthen").
	// removes unnecessary levels on names
	/*
	var unWeaken = function( g, t ){
		var i = 0;
		var x = null;
console.debug( '\t\tunWeaken: '+t );
		while( g !== null ){
			// fetches the type of the variable
			x = g.getType( 0 );
			if( x === undefined )
				break;


			// variable should be at index 0, thus
			// we shift the variable to current depth
			x = shift( x, 0, i );
			// if variable does not occur in t, then
			// unshift all values before that one
			if( isFree( x, t ) ){
				t = shift( t, i, -1 );
			}
console.debug( '\t\t'+i+'--: '+t );
			g = g.endScope();
			++i;
		}
console.debug( '\t\tdone: '+t );
		return t;
	}
	*/

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

	//
	// Protocol Conformance
	//

	var Work = function( g, s, p, q ){
		return { g: g, s: s, p: p, q: q };
	}

	var checkConformance = function( g, s, p, q ){
		var work = [ Work(g, s, p, q) ];
		var visited = [];
		return checkConformanceAux( work, visited );
	}

	var checkConformanceAux = function( work, visited ){

var i=0;
console.debug( '' );
		while( work.length > 0 ){
			var w = work.pop();

			if( !contains( visited, w ) ){
				var g = w.g;
				var s = w.s;
				var p = w.p;
				var q = w.q;

console.debug( (i++)+' : '+s+' >> '+p+' || '+q );
			
				var left = step( g, s, p, q, true );
				var right = step( g, s, q, p, false );
				if( left === null || right === null )
					return null; // fails

				work = work.concat(left).concat(right);

				visited.push( w );
			}
		}
		return visited;
	}

	// returns: potentially empty array of work or null
	var step = function( g, s, p, q, isLeft ){
		s = unfold(s); // I don't like this
		p = unfold(p); // I don't like this

		var W = function( g, s, p ){
			if( isLeft )
				return Work( g, s, p, q );
			else
				return Work( g, s, q, p );
		};

		//
		// break down of STATE
		//

		if( s.type === types.AlternativeType ){
			var ss = s.inner();
			var res = [];
			// protocol must consider *all* cases
			for( var i=0; i<ss.length; ++i ){
				var tmp = step( g, ss[i], p, q, isLeft );
				// one failed!
				if( tmp === null )
					return null;
				res = res.concat(tmp);
			}
			return res;
		}
		if( s.type === types.IntersectionType ){
			var ss = s.inner();
			// protocol only needs to consider *one* case
			for( var i=0; i<ss.length; ++i ){
				var tmp = step( g, ss[i], p, q, isLeft );
				// one step, we are done
				if( tmp !== null )
					return tmp;
			}
			// did not find a good step, fail.
			return null;
		}

		//
		// break down of PROTOCOL
		//

		// by (step:None)
		if( p.type === types.NoneType ){
			// no need to add new work, we already know this configuration steps
			return [];
		}

		// by (step:Alternative)
		if( p.type === types.AlternativeType ){
			var pp = p.inner();
			// protocol only needs to consider *one* case
			for( var i=0; i<pp.length; ++i ){
				var tmp = step( g, s, pp[i], q, isLeft );
				// one step, we are done
				if( tmp !== null )
					return tmp;
			}
			// did not find a good step, fail.
			return null;
		}
		if( p.type === types.IntersectionType ){
			var pp = p.inner();
			var res = [];
			// protocol must consider *all* cases
			for( var i=0; i<pp.length; ++i ){
				var tmp = step( g, s, pp[i], q, isLeft );
				// one failed!
				if( tmp === null )
					return null;
				res = res.concat(tmp);
			}
			return res;
		}

		// by (step:Recovery) of non-protocol states.
		if( s.type !== types.RelyType && equals(s,p) ){
			return [ W( g, NoneType, NoneType ) ];
		}

		//
		// Protocol Stepping
		//

		// by (step:SimProtocol) --- FIXME: changes must be reflected on draft!
		if( s.type === types.RelyType && p.type === types.RelyType &&
			subtype( s.rely(), p.rely()) ){

			// check 's' and 'o' guarantee: ( G ; R )
			var gs = s.guarantee();
			var gp = p.guarantee();
			// must account for omitted guarantee (i.e.: G == G ; none)
			if( gs.type !== types.GuaranteeType ){
				gs = new GuaranteeType( gs, NoneType );
			}
			if( gp.type !== types.GuaranteeType ){
				gp = new GuaranteeType( gp, NoneType );
			}

			if( equals( gs.guarantee(), gp.guarantee() ) ){
				return [ W( g, gs.rely(), gp.rely() ) ];
			}
		}

		//
		// State Stepping
		//
		
		// attempts to find matching type/location to open existential
		if( p.type === types.ExistsType ){
// TODO: check bound?
			// by (step:Open-Type)
			// by (step:Open-Loc)
			var u = unifyState( s, p );
console.debug( '\t\t'+p.toString()+'\t\t>> '+u.toString() );
			// substitute, check bound

			return step( g, s, u, q, isLeft );
		}

//TODO wasn't this suppose to be subtypign instead of 'equals'?
		if( p.type === types.RelyType && subtype( s, p.rely() ) ){
			// case analysis on the guarantee type, 'b'
			var b = p.guarantee();

			// by (step:Step)
			if( b.type === types.GuaranteeType ){
				return [ W( g, b.guarantee(), b.rely() ) ];
			}
		
			// by (step:Step-Type)
			// by (step:Step-Loc)
			if( b.type === types.ForallType ){
				var i = b.inner();
				var id = b.id();
				var name = id.name();
				var bound = b.bound();

				// indexes remain unchanged for this protocol, because we pushed the
				// forall declaration declaration to gamma. However, the other protocol
				// must be shifted to preserve its index.
				q = shift( q, 0, 1 );
				g = g.newScope( name, id, bound );
				s = i.guarantee(); // state
				p = i.rely(); //step

				if( isLeft )
					return [ Work( g, s, p, q ) ];
				else
					return [ Work( g, s, q, p ) ];
			}

			// assume case is that of omitted '; none' a 'b' is the new state.
			// assume that type was previously checked to be well-formed.
			return [ W( g, b, NoneType ) ];
		}

		return null;
	}

		/*
TODO: missing cases.	
	// forall
	if $p = A_0 => \forall X <: A_1. ( A_2 ; P ) $ and $q = A_0 => \forall X <: A_1 .( A_2 ; Q )$ then
		work.add( ($\Gamma, X : \kb{type}, X <: A_1$), $P$, $Q$ ); // by (step:SimForallType)
		return true
	
	if $p = A_0 => \forall t. ( A_1 ; P ) $ and $q = A_0 => \forall t.( A_1 ; Q )$ then
		work.add( ($\Gamma, t : \kb{loc}$), $P$, $Q$ ); // by (step:SimForallLoc)
		return true

	// exists
	if $p = \exists t.P $ and $q = \exists t.Q$ then
		return stepSim( ($\Gamma, t : \kb{loc}$), $P$, $Q$ ) // by (step:SimExistsLoc)

	if $p = \exists X <: A.P $ and $q = \exists X <: A.Q$ then
		return stepSim( ($\Gamma, X : \kb{type}, X <: A$), $P$, $Q$ ) // by (step:SimExistsType)

	// application
	if $p = A => \forall X <: D.P $ and $q = A => Q$ and unify($Q$, $P$, $X$) = $D'$ and $\Gamma |- D' <: D$ then
		return stepSim( $\Gamma$, $P\{D'/X\}$, $Q$ ) // by (step:SimTypeApp)
		
	if $p = A => \forall t.P $ and $q = A => Q$ and unify($Q$, $P$, $t$) = $t'$ then
		return stepSim( $\Gamma$, $A => P\{t'/t\}$, $A => Q$ ) // by (step:SimLocApp)
	*/

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

				//assert( wfProtocol( left ) || ('Invalid protocol: '+left ) , ast.a );
				//assert( wfProtocol( right ) || ('Invalid protocol: '+right ) , ast.b );

				// Protocol conformance, goes through all possible "alias
				// interleaving" and ensure all those possibilities are considered
				// in both protocols.

				var table = checkConformance( env, cap, left, right );
				var res = table !== null ; // is valid if table not null
				// checkProtocolConformance(cap, left, right, ast);
				
				assert( ast.value === res || ('Unexpected Result, got '+res+' expecting '+ast.value) , ast);
				
//FIXME return type should depend on the kind of node: types -> type , construct -> some info.
				// returns an array or null
				return table;
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
						// indexes MUST go [ n, n-1, ..., 1, 0 ] to match the
						// desired depth of the DeBruijn indexes.
						var n = pars[j];
						args[j] = isTypeVariableName(n) ? 
							new TypeVariable(n,(pars.length-j-1),null) :
							new LocationVariable(n,(pars.length-j-1));
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
// FIXME needs to ensure that definition is not a locationvariable?
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

			// this is a very hackish way to extract conformance table without
			// breaking the inner return type signature!
			if( ast.kind === AST.SHARE ){
				// unit
				return UnitType;
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

