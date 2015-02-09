// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

/**
 * INCLUDE typechecker.types.js
 *  TypeChecker : stuff in typechecker.types.js
 */

var TypeChecker = (function( exports ){

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

	// unify 'x' in 't' to match 'a'
	var unify = function( x,t, a ){
		if( x.type !== types.LocationVariable && 
			x.type !== types.TypeVariable ){
			error( "@unify: can only unify a Type/LocationVariable, got: "+x.type );
		}

		return unifyAux( x,t,a, new Set() );
	};

	// Search to find a UNIQUE match:
	// returns 'false' is types are incompatible,
	// returns 'type' if match is found,
	// returns 'true' if match not found but types are equal.
	var unifyAux = function( x, t, a, trail ){
		
		// base case: variable 'x' is found in 't'
		if( x.type === t.type && x.index() === t.index() && (
			// unified type must match x's kind
			( x.type === types.LocationVariable && a.type === types.LocationVariable ) ||
			( x.type === types.TypeVariable && a.type !== types.LocationVariable ) ) )
			return a;

		// if mismatch on DefinitionType
		var deft = t.type === types.DefinitionType;
		var defa = a.type === types.DefinitionType;

		if( deft || defa ){
			var key = t.toString(true) + a.toString(true);

			// assume no match on cycles, but types OK.
			if( trail.has(key) )
				return true;

			trail.add(key);
			t = deft ? unfold(t) : t;
			a = defa ? unfold(a) : a;

			return unifyAux( x, t, a, trail );
		}

		// no match a this level, attempt further down.

		if( t.type !== a.type )
			return false; // failed to match

		var tmp = true;
		
		// returns whether it should abort, leaves result in 'tmp'
		var aux = function( value ){
			
			// must use '=== false' to avoid conversions
			// already failed, keeps with false.
			if( tmp === false || value === false ){
				tmp = false;
				return false;
			}
			
			if( tmp === true ){
				tmp = value;
				return true;
			}
			
			// 'value' is not a type, no need for equality check
			if( value === true )
				return true;

			// 'tmp' is not 'false' nor 'true', should be valid type!
			// 'value' is not 'false' nor 'true', shoud be valid type too!
			// they must be equal, or unification fails.
			return equals( tmp, value );
		}

		switch( t.type ){
			case types.FunctionType: {
				if( !aux( unifyAux( x, t.argument(), a.argument(), trail ) )||
					!aux( unifyAux( x, t.body(), a.body(), trail ) ) )
					return false;
				return tmp;
			}

			case types.BangType:
				return unifyAux( x, t.inner(), a.inner(), trail );

			case types.RelyType:
			case types.GuaranteeType: {
				if( !aux( unifyAux( x, t.rely(), a.rely(), trail ) ) ||
					!aux( unifyAux( x, t.guarantee(), a.guarantee(), trail ) ) )
					return false;
				return tmp;
			}

			case types.SumType:{
				var ts = t.tags();
				var as = a.tags();

				if( ts.size !== as.size )
					return false;

				for( var k of ts.keys() ){
					if( !as.has(k) ||
						!aux( unifyAux( x, ts.get(k), as.get(k), trail ) ) )
						return false;
				}

				return tmp;
			}

			case types.AlternativeType:
			case types.IntersectionType:
			case types.StarType: {
				var ts = t.inner();
				var as = a.inner();

				// ts has more elements then it is impossible to match
				// however, it can have LESS since it could match more than one type
				// such as A*B, A(+)B, etc.
				if( ts.length > as.length )
					return false;

				var tt = null;
				var tcount = 0;
				var as = as.slice(0); // copies array

				// compute difference between sets, there must be only one in 't'
				for( var i=0; i<ts.length; ++i ){
					var found = false;
					for( var j=0; j<as.length; ++j ){
						if( equals( ts[i], as[j] ) ){
							as.splice(j,1); // removes element
							found = true;
							break;
						}
					}
					if( !found ){
						if( tt !== null && !equals( tt, ts[i] ) ){
							return false;
						}
						tt = ts[i];
						tcount += 1;
					}
				}

				if( as.length === 0 ){
					// unification type is empty, which is OK.
					return true;
				}
				//else: i.e. as.length > 0

				if( tt === null || tcount === 0 ){
					// we have some types that did not match, but we do not have
					// a single matching type in 't'. Fail.
					return false;
				}

				if( tcount > 1 ){

					// we cannot divide the remaining elements over equivalent sets of tt
					if( as.length % tcount !== 0 )
						return false;

					var cs = new Array( as.length );
					for( var i=0; i<as.length; ++i ){
						cs[i] = 1; // count i position as 1 occurance
						for( var j=i+1; j<as.length; ++j ){
							if( equals( as[i], as[j] ) ){
								cs[i] += 1; 
								as.splice(j,1);
								--j;
							}
						}
					}

					for( var i=0; i<as.length; ++i ){
						// not divisible by tcounts.
						if( cs[i] % tcount !== 0 )
							return false;
					}
				}

				var tmp = new t.constructor();
				for( var i=0; i<as.length; ++i ){
					tmp.add( as[i] );
				}

				// careful! but this should not recur on this case because
				// we broke down 't' into 'tt' which should just be a single
				// type that did not match anything in 't'.
				return unifyAux( x, tt, tmp, trail );
			}

			// order matters for tuples
			case types.TupleType: {
				var ts = t.inner();
				var as = a.inner();

				if( ts.length !== as.length )
					return false;

				for( var i=0; i<ts.length; ++i ){
					if( !aux( unifyAux( x, ts[i], as[i], trail ) ) )
						return false;
				}

				return tmp;
			}

			case types.ExistsType:
			case types.ForallType: {
				var tb = t.bound();
				var ab = a.bound();

				// either have inconsistent 'null'
				if( ( tb === null ^ ab === null ) || 
				// or not null, but have invalid matching
					( tb ===null && ab === null && !aux( unifyAux( x, tb, ab, trail ) ) ) )
					return false;
				
				// going inside an existential, we must shift 'x' index
				var xi = shift1(x,0);

				// these remain intentionally unchanged
				var ti = t.inner();
				var ai = a.inner();

				if( !aux( unifyAux( xi, ti, ai, trail ) ) )
					return false;

				return tmp;
			}

			case types.ReferenceType: {
				return unifyAux( x, t.location(), a.location(), trail );
			}

			case types.StackedType: {
				if( !aux( unifyAux( x, t.left(), a.left(), trail ) ) ||
					!aux( unifyAux( x, t.right(), a.right(), trail ) ) )
					return false;
				return tmp;
			}

			case types.CapabilityType: {
				if( !aux( unifyAux( x, t.location(), a.location(), trail ) ) ||
					!aux( unifyAux( x, t.value(), a.value(), trail ) ) )
					return false;
				return tmp;
			}

			case types.RecordType: {
				var ts = t.fields();
				var as = a.fields();

				if( ts.size !== as.size )
					return false;

				for( var k of ts.keys() ){
					if( !as.has(k) ||
						!aux( unifyAux( x, ts.get(k), as.get(k), trail ) ) )
						return false;
				}

				return tmp;
			}

			case types.LocationVariable:
			case types.TypeVariable:
				return t.index() === a.index();

			case types.PrimitiveType:
				return t.name() === a.name();

			case types.NoneType:
			case types.TopType:
				return true;

			default:
				error( "@unifyAux: Not expecting " +t.type );
		}
	};


	// shifts indexes of free variables in 't' by 'd'.
	// t -> type
	// c -> cutoff index
	// d -> shift value
	var shift = function( t, c, d ){

		switch ( t.type ){

			case types.FunctionType:
				return new FunctionType(
						shift( t.argument(), c, d ),
						shift( t.body(), c, d ) );

			case types.BangType:
				return new BangType( shift( t.inner(), c, d ) );

			case types.RelyType: 
				return new RelyType(
							shift( t.rely(), c, d ),
							shift( t.guarantee(), c, d ) );

			case types.GuaranteeType:
				return new GuaranteeType(
							shift( t.guarantee(), c, d ),
							shift( t.rely(), c, d ) );

			case types.SumType:{
				var sum = new SumType();
				t.tags().forEach( 
					function(value,key){
						sum.add( key, shift( value, c, d ) );
					} );
				return sum;
			}

			case types.AlternativeType:
			case types.IntersectionType:
			case types.StarType: 
			case types.TupleType: {
				var star = new t.constructor();
				var inners = t.inner();
				for( var i=0;i<inners.length;++i ){
					star.add( shift( inners[i], c, d ) );
				}	
				return star;
			}

			case types.ExistsType:
			case types.ForallType:{
				// calls appropriate constructor function
				return new t.constructor( t.id(), 
						shift( t.inner(), c+1, d ),
						( t.bound() !== null ? shift( t.bound(), c, d ) : null )
						);
			}

			case types.ReferenceType:
				return new ReferenceType( shift( t.location(), c, d ) );
			
			case types.StackedType:
				return new StackedType( shift( t.left(), c, d ), shift( t.right(), c, d ) );

			case types.CapabilityType:
				return new CapabilityType( shift( t.location(), c, d ), shift( t.value(), c, d ) );
			
			case types.RecordType: {
				var r = new RecordType();
				t.fields().forEach(
					function(value,key){
						r.add( key, shift( value, c, d ) );
					});
				return r;
			}

			case types.DefinitionType: {
				var fs = t.args();
				var tmp = new Array( fs.length );
				for( var i=0; i<fs.length; ++i )
					tmp[i] = shift( fs[i], c, d );
				return new DefinitionType( t.definition(), tmp, t.getTypeDef() );
			}

			case types.LocationVariable:
			case types.TypeVariable:
				if( t.index() < c )
					return t;
				return t.copy( t.index()+d );

			case types.PrimitiveType:
			case types.NoneType:
			case types.TopType:
				return t;
			default:
				error( "@shift: Not expecting " +t.type );
		}
	};

	var shift1 = function( t, c ){
		return shift( t, c, 1 );
	};


	var keyF = function( a, b ){
		
		var rebase = function( a ){
			var s = indexSet(a);
			if( s.size > 0 ){
				var v = [];
				s.forEach( function(val){ v.push(val); });
				v.sort();

				for( var i=0; i<v.length; ++i ){
					if( v[i] !== i ){
						a = shift( a, i, i-v[i] );
					}
				}
			}
			return a;
		};

//console.log('>>'+ a.toString(true) + b.toString(true) );
		a = rebase(a);
		b = rebase(b);
//console.log('<<'+ a.toString(true) + b.toString(true) );

		return a.toString(true) + b.toString(true);

	};


	/**
	 * Tests if types 'a' and 'b' are the same.
	 * Up to renaming of bounded variables, so that it renames existentials
	 * and foralls. Thus, returns true when they are structurally equal, even
	 * if their labels in existentials are of different strings values.
	 * @param {Type} a
	 * @param {Type} b
	 * @return {Boolean} if the types are equal up to renaming.
	 */
	var equals = function( t1, t2 ){
		return equalsAux( t1, t2, new Set() );
	};

	var equalsAux = function( t1, t2, trail ){

		if( t1 === t2 )
			return true;

		// if mismatch on DefinitionType
		var def1 = t1.type === types.DefinitionType;
		var def2 = t2.type === types.DefinitionType;

		if( def1 || def2 ){

			var key = keyF(t1,t2);

			// algorithm based on "Subtyping Recursive Types".
			if( trail.has(key) )
				return true;

			trail.add(key);
			t1 = def1 ? unfold(t1) : t1;
			t2 = def2 ? unfold(t2) : t2;

			return equalsAux( t1, t2, trail );
		}
		
		if( t1.type !== t2.type )
			return false;
			
		// assuming both same type
		switch ( t1.type ){
			case types.ForallType:		
			case types.ExistsType: {
				if( t1.id().type !== t2.id().type )
					return false;

				return equalsAux( t1.bound(), t2.bound(), trail ) &&
					equalsAux( t1.inner(), t2.inner(), trail );
			}
			case types.TypeVariable:
			case types.LocationVariable: {
				return  t1.index() === t2.index();
			}
			case types.FunctionType:
				return equalsAux( t1.argument(), t2.argument(), trail ) &&
					equalsAux( t1.body(), t2.body(), trail );
			case types.BangType:
				return equalsAux( t1.inner(), t2.inner(), trail );
			case types.RelyType: {
				return equalsAux( t1.rely(), t2.rely(), trail ) &&
					equalsAux( t1.guarantee(), t2.guarantee(), trail );
			}
			case types.GuaranteeType: {
				return equalsAux( t1.guarantee(), t2.guarantee(), trail ) &&
					equalsAux( t1.rely(), t2.rely(), trail );
			}
			case types.SumType: {
				var t1s = t1.tags();
				var t2s = t2.tags();

				if( t1s.size !== t2s.size )
					return false;

				for( var k of t1s.keys() ){
					if( !t2s.has(k) ||
						!equalsAux( t1s.get(k), t2s.get(k), trail ) )
						return false;
				}
				return true;
			}
			case types.ReferenceType:
				return equalsAux( t1.location(), t2.location(), trail );
			case types.StackedType:
				return equalsAux( t1.left(), t2.left(), trail ) &&
					equalsAux( t1.right(), t2.right(), trail );
			case types.CapabilityType:
				return equalsAux( t1.location(), t2.location(), trail ) &&
					equalsAux( t1.value(), t2.value(), trail );
			case types.RecordType: {
				var t1s = t1.fields();
				var t2s = t2.fields();

				if( t1s.size !== t2s.size )
					return false;

				for (var k of t2s.keys() ) {
					if( !t1s.has(k) || 
						!equalsAux( t1s.get(k), t2s.get(k), trail ) )
						return false;
				}

				return true;
			} 
			case types.TupleType: {
				var t1s = t1.inner();
				var t2s = t2.inner();
				if( t1s.length !== t2s.length )
					return false;
				for( var i=0;i<t1s.length;++i )
					if( !equalsAux( t1s[i], t2s[i], trail ) )
						return false;
				return true;
			}
			case types.PrimitiveType:
				return t1.name() === t2.name();

			case types.IntersectionType:
			case types.AlternativeType:
			case types.StarType:{
				var i1s = t1.inner();
				var i2s = t2.inner();
				
				if( i1s.length !== i2s.length )
					return false;
				// any order should do
				var tmp_i2s = i2s.slice(0); // copies array
				for(var i=0;i<i1s.length;++i){
					var curr = i1s[i];
					var found = false;
					// tries to find matching element
					for(var j=0;j<tmp_i2s.length;++j){
						var tmp = tmp_i2s[j];
						if( equalsAux( curr, tmp, trail ) ){
							tmp_i2s.splice(j,1); // removes element
							found = true;
							break; // continue to next
						}
					}
					// if not found, then must be different
					if( !found ){
						return false;
					}
				}
				return true;
			}

			default:
				error( "@equals: Not expecting " +t2.type );
			}
	};

	/**
	 * Substitutes in 't' any occurances of 'from' to 'to'
	 * 		t[from/to] ('from' for 'to')
	 * @param {Type} 't' that is to be searched on
	 * @param {LocationVariable,TypeVariable} when 'from' is found, it is replaced with
	 *  	NOTE: 'from' is limited to LocationVariable or TypeVariables
	 * @param {Type} 'to'
	 * @param {Function} equals function to compare types
	 * @return a new 'type' where all instances of 'from' have been replaced with 'to'.
	 */
	var substitutionAux = function(t,from,to){
		
		// for convenience...
		var rec = function(type){
			return substitutionAux(type,from,to);
		}
		
		// base case: if X{to/X} = to and since we are only checking location
		// variables or type variables, we only need to check the index.
		if( t.type === from.type && t.index() === from.index() )
			return to;
			
		switch ( t.type ){
		case types.FunctionType:
			return new FunctionType( rec(t.argument()), rec(t.body()) );
		case types.BangType:
			return new BangType( rec(t.inner()) );
		case types.RelyType:
			return new RelyType( rec(t.rely()), rec(t.guarantee()) );
		case types.GuaranteeType:
			return new GuaranteeType( rec(t.guarantee()), rec(t.rely()) );

		case types.SumType:{
			var sum = new SumType();
			t.tags().forEach(
				function(value,key){
					sum.add( key, rec(value) );
				} );
			return sum;
		}
		
		case types.AlternativeType:
		case types.IntersectionType:
		case types.StarType:
		case types.TupleType: {
			var star = new t.constructor();
			var inners = t.inner();
			for( var i=0;i<inners.length;++i ){
				star.add( rec(inners[i]) ); 
			}	
			return star;
		}

		case types.ExistsType: 
		case types.ForallType: {
			var nvar = t.id();
			var ninner = t.inner();
			// this is before we shift
			var nbound = t.bound();
			if( nbound !== null ){
				nbound = substitutionAux(nbound,from,to);
			}

			// updates the indexes (see Types and Programming Languages, Chapter 6)
			var _to = shift1(to,0);
			var _from = shift1(from,0);

			// to avoid having to switch again, we just use 't' constructor function
			return new t.constructor( nvar, substitutionAux(ninner,_from,_to), nbound );
		}
		case types.ReferenceType:
			return new ReferenceType( rec(t.location()) );
		case types.StackedType:
			return new StackedType( rec(t.left()), rec(t.right()) );
		case types.CapabilityType:
			return new CapabilityType( rec(t.location()), rec(t.value()) );
		case types.RecordType: {
			var r = new RecordType();
			t.fields().forEach(
				function(value,index){
					r.add( index, rec(value) );
				});
			return r;
		}
		case types.DefinitionType: {
			var fs = t.args();
			var tmp = new Array( fs.length );
			for( var i=0; i<fs.length; ++i )
				tmp[i] = rec(fs[i]);
			return new DefinitionType(t.definition(),tmp,t.getTypeDef());
		}

		// these remain UNCHANGED
		// note that Location/Type Variable is tested ABOVE, not here
		case types.LocationVariable:
		case types.TypeVariable:
		case types.PrimitiveType:
		case types.NoneType:
		case types.TopType:
			return t;

		default:
			error( "@substitutionAux: Not expecting " +t.type );
		}
	};

	// =================================
	
	
	/*
	 * This is a "simpler" substitution where 'from' must either be a
	 * LocationVariable or a TypeVariable. This restriction simplifies the
	 * equality test since we are no longer attempting to match complete types
	 * and instead are just looking for TypeVariables or LocationVariables
	 */
	var substitution = function(type,from,to){
		if( from.type !== types.LocationVariable && 
			from.type !== types.TypeVariable ){
			error( "@substitution: can only substitute a Type/LocationVariable, got: "+from.type );
		}

		return substitutionAux(type,from,to);
	};
	
	/**
	 * Subtyping two types.
	 * @param {Type} t1
	 * @param {Type} t2
	 * @return {Boolean} true if t1 <: t2 (if t1 can be used as t2).
	 */
	 var subtype = function( t1, t2 ){
	 	return subtypeAux( t1, t2, new Set() );
	 };

	var subtypeAux = function( t1 , t2, trail ){

		if( t1 === t2 || equals(t1,t2) ) // A <: A
			return true;
		
		// if mismatch on DefinitionType
		var def1 = t1.type === types.DefinitionType;
		var def2 = t2.type === types.DefinitionType;

		if( def1 || def2 ){

			var key = keyF(t1,t2);

			// algorithm based on "Subtyping Recursive Types".
			if( trail.has(key) )
				return true;

			trail.add(key);
			t1 = def1 ? unfold(t1) : t1;
			t2 = def2 ? unfold(t2) : t2;

			return subtypeAux( t1, t2, trail );
		}

		if( t2.type === types.TopType && t1.type !== types.LocationVariable )
			return true;

		// if X <: A is in environment
		if( t1.type === types.TypeVariable ){
			var bound = t1.bound();

			if( bound !== null && equals( bound, t2 ) )
				return true;
		}

		// "pure to linear" - ( t1: !A ) <: ( t2: A )
		if ( t1.type === types.BangType && t2.type !== types.BangType )
			return subtypeAux( t1.inner(), t2, trail );
	
		// types that can be "banged"
		if ( t2.type === types.BangType &&
			( t1.type === types.ReferenceType
			|| t1.type === types.PrimitiveType
			|| ( t1.type === types.RecordType && t1.isEmpty() ) ) )
			return subtypeAux( t1, t2.inner(), trail );
			
		// "ref" t1: (ref p) <: !(ref p)
		if ( t1.type === types.ReferenceType && t2.type === types.BangType )
			return subtypeAux( t1, t2.inner(), trail );
		
		if( t1.type !== types.AlternativeType && t2.type === types.AlternativeType ){
			// only requirement is that t1 is one of t2's alternative
			var i2s = t2.inner();
			for(var j=0;j<i2s.length;++j) {
				if( subtypeAux( t1, i2s[j], trail ) ){
					return true;
				}
			}
			return false;
		}
		
		if( t1.type === types.IntersectionType && t2.type !== types.IntersectionType ){
			// one of t1s alts is t2
			var i1s = t1.inner();
			for(var j=0;j<i1s.length;++j) {
				if( subtypeAux( i1s[j], t2, trail ) ){
					return true;
				}
			}
			return false;
		}

		if( t2.type === types.ExistsType && t1.type !== types.ExistsType ){
			// must shift 't1' to match 't2' depth
			var t1_s = shift1( t1, 0 );

			// if found unification and it obeys bound, successed.
			var u = unify( t2.id(), t2.inner(), t1_s );

			// must use '===' to avoid implicit conversions
			if( u === false )
				return false;
			if( u === true )
				// no need to check bounds because match was empty (but valid)
				return true;
			// else 'u' must be a type
			var b = t2.bound();
			return b === null || subtypeAux( u, b, trail );
		}
		
		if( t1.type === types.ForallType && t2.type !== types.ForallType ){
			// must shift 't2' to match 't1' depth
			var t2_s = shift1( t2, 0 );

			var u = unify( t1.id(), t1.inner(), t2_s );
			
			// must use '===' to avoid implicit conversions
			if( u === false )
				return false;
			if( u === true )
				// no need to check bounds because match was empty (but valid)
				return true;
			// else 'u' must be a type
			var b = t1.bound();
			return b === null || subtypeAux( u, b, trail );
		}

		// all remaining rule require equal kind of type
		if( t1.type !== t2.type ){
			return false;
		}
			
		//else: safe to assume same type from here on
		switch ( t1.type ){
			case types.NoneType:
				return true;
			case types.PrimitiveType:
				return t1.name() === t2.name();
			case types.BangType:
				// if t2 is unit: "top" rule
				if( t2.inner().type === types.RecordType && t2.inner().isEmpty() )
					return true;
				return subtypeAux( t1.inner(), t2.inner(), trail );
			case types.ReferenceType:
				return subtypeAux( t1.location(), t2.location(), trail );

			// we do not subtype inside a rely or guarantee type. thus, if this type
			// appears here (after checking for equality) it must be 'false'
			case types.RelyType: 
			case types.GuaranteeType:
				return false

			case types.FunctionType:
				return subtypeAux( t2.argument(), t1.argument(), trail )
					&& subtypeAux( t1.body(), t2.body(), trail );
			case types.RecordType:{
				if( !t1.isEmpty() && t2.isEmpty() )
					return false;

				// all fields of t2 must be in t1
				var t1fields = t1.fields();
				var t2fields = t2.fields();				
				for( var k of t2fields.keys() ){
					if( !t1fields.has(k) ||
						!subtypeAux( t1fields.get(k), t2fields.get(k), trail ) ){
						return false;
					}
				}
				return true;
			}
			case types.TupleType: {
				var t1s = t1.inner();
				var t2s = t2.inner();
				if( t1s.length !== t2s.length )
					return false;
				for( var i=0;i<t1s.length;++i )
					if( !subtypeAux( t1s[i], t2s[i], trail ) )
						return false;
				return true;
			}

			case types.StackedType:
				return subtypeAux( t1.left(), t2.left(), trail ) &&
					subtypeAux( t1.right(), t2.right(), trail );

			case types.AlternativeType:{
				var i1s = t1.inner();
				var i2s = t2.inner();
				
				// more alternatives in t1
				if( i1s.length > i2s.length )
					return false;
					
				// any order will do, but must ensure all of t1 is inside t2
				var tmp_i2s = i2s.slice(0); // copies array
				for(var i=0;i<i1s.length;++i){
					var curr = i1s[i];
					var found = false;
					for(var j=0;j<tmp_i2s.length;++j){
						var tmp = tmp_i2s[j];
						if( subtypeAux( curr, tmp, trail ) ){
							tmp_i2s.splice(j,1); // removes element
							found = true;
							break; // continue to next
						}
					}
					if( !found )
						return false;
				}
				return true;
			}
			//opposite of alternative type
			case types.IntersectionType:{
				// note intentionally inverts order, rest copy pasted from above.
				var i1s = t2.inner();
				var i2s = t1.inner();
				
				// more alternatives in t1
				if( i1s.length > i2s.length )
					return false;
					
				// any order will do, but must ensure all of t1 is inside t2
				var tmp_i2s = i2s.slice(0); // copies array
				for(var i=0;i<i1s.length;++i){
					var curr = i1s[i];
					var found = false;
					for(var j=0;j<tmp_i2s.length;++j){
						var tmp = tmp_i2s[j];
						if( subtypeAux( curr, tmp, trail ) ){
							tmp_i2s.splice(j,1); // removes element
							found = true;
							break; // continue to next
						}
					}
					if( !found )
						return false;
				}
				return true;
			}
			case types.StarType:{
				var i1s = t1.inner();
				var i2s = t2.inner();
				
				if( i1s.length !== i2s.length )
					return false;
				// for *-type, any order will do
				var tmp_i2s = i2s.slice(0); // copies array
				for(var i=0;i<i1s.length;++i){
					var curr = i1s[i];
					var found = false;
					for(var j=0;j<tmp_i2s.length;++j){
						var tmp = tmp_i2s[j];
						if( subtypeAux( curr, tmp, trail ) ){
							tmp_i2s.splice(j,1); // removes element
							found = true;
							break; // continue to next
						}
					}
					if( !found )
						return false;
				}
				return true;
			}
			case types.SumType:{
				var i1s = t1.tags();
				var i2s = t2.tags();
				for( var k of i1s.keys() ){
					if( !i2s.has(k) || // if tag is missing, or
						!subtypeAux( i1s.get(k), i2s.get(k), trail ) )
						return false;
				}
				return true;
			}
			case types.CapabilityType:
				return subtypeAux( t1.location(), t2.location(), trail ) &&
					subtypeAux( t1.value(), t2.value(), trail );
				
			case types.ForallType:		
			case types.ExistsType:{
				
				if( t1.id().type !== t2.id().type )
					return false;
				if( !equals( t1.bound(), t2.bound() ) )
					return false;
				
				return subtypeAux( t1.inner(), t2.inner(), trail );
			}

			case types.TypeVariable:
			case types.LocationVariable:
				return t1.index() === t2.index();

			default:
				error( "@subtypeAux: Not expecting " +t1.type );
		}

	};

	
	var isFree = function( x, t ){
		if( x.type !== types.LocationVariable && 
			x.type !== types.TypeVariable ){
			error( "@isFree: can only check a Type/LocationVariable, got: "+x.type );
		}
		return isFreeAux( x, t, new Set() );
	};

	var isFreeAux = function( x, t, trail ){

		if( t.type === types.DefinitionType ){
			var key = t.toString(true);

			// if there is a cycle, assume 'x' is free
			if( trail.has(key) )
				return true;

			trail.add(key);

			return isFreeAux( x, unfold(t), trail );
		}

		switch ( t.type ){
			case types.NoneType:
			case types.PrimitiveType:
				return true;

			case types.BangType:
				return isFreeAux( x, t.inner(), trail );
				
			case types.ReferenceType:
				return isFreeAux( x, t.location(), trail );

			case types.RelyType: {
				return isFreeAux( x, t.rely(), trail ) &&
					isFreeAux( x, t.guarantee(), trail );
			}
			case types.GuaranteeType: {
				return isFreeAux( x, t.guarantee(), trail ) &&
					isFreeAux( x, t.rely(), trail );
			}
			case types.FunctionType:
				return isFreeAux( x, t.argument(), trail )
					&& isFreeAux( x, t.body(), trail );
			case types.RecordType:{
				var fields = t.fields();
				for( var k of fields.keys() ){
					if( !isFreeAux( x, fields.get(k), trail ) )
						return false;
				}
				return true;
			}
			case types.StackedType:
				return isFreeAux( x, t.left(), trail ) &&
					isFreeAux( x, t.right(), trail );
			case types.CapabilityType:
				return isFreeAux( x, t.location(), trail ) &&
					isFreeAux( x, t.value(), trail );

			case types.AlternativeType:
			case types.IntersectionType:
			case types.StarType:
			case types.TupleType: {
				var ts = t.inner();
				for( var i=0;i<ts.length;++i )
					if( !isFreeAux( x, ts[i], trail ) )
						return false;
				return true;
			}

			case types.SumType:{
				var ts = t.tags();
				for( var k of ts.keys() ){
					if( !isFreeAux( x, ts.get(k), trail ) )
						return false;
				}
				return true;
			}
			case types.ForallType:		
			case types.ExistsType:{
				return ( t.bound() === null || isFreeAux( x, t.bound(), trail ) ) &&
					// shifts 'x' by 1 when moving inside a forall/exists
					isFreeAux( shift(x,0,1), t.inner(), trail );
			}

			case types.TypeVariable:
			case types.LocationVariable:
				return x.type !== t.type || x.index() !== t.index();

			default:
				error( "@isFreeAux: Not expecting " +t1.type );
		}
	};
	
	// unfolds DefinitionType until it reaches some useful type
	// NOTE: we previously checked for infinitely recursive definitions
	// therefore this function should always terminate.
	var unfold = function(t){
		while( t.type === types.DefinitionType ){			
			t = unfoldDefinition(t);
		}
		return t;
	};
	
	var unfoldDefinition = function(d){
		if( d.type !== types.DefinitionType )
			return d;
		var t = d.getDefinition();
		var args = d.args();
		var pars = d.getParams();
		// type definitions will only replace Type or Location Variables, we
		// can use the simpler kind of substitution.
		for(var i=(args.length-1);i>=0;--i){
			t = substitution(t,pars[i],args[i]);
		}
		// since a typedef does not have enclosing environment, we do not need to
		// shift by -1 for type 't' as it does not have free variables here.
		return t;
	};

	//returns set with index levels from 0.
	var indexSet = function( t ){
		var set = new Set();
		indexSetAux( t, 0, set );
		return set;
	};

	var indexSetAux = function( t, c, set ){

		switch ( t.type ){
			case types.BangType:{
				indexSetAux( t.inner(), c, set );
				return;
			}
			case types.ReferenceType:{
				indexSetAux( t.location(), c, set );
				return;
			}
			case types.RelyType:
			case types.GuaranteeType: {
				indexSetAux( t.rely(), c, set );
				indexSetAux( t.guarantee(), c, set );
				return;
			}
			case types.FunctionType:{
				indexSetAux( t.argument(), c, set );
				indexSetAux( t.body(), c, set );
				return;
			}
			case types.RecordType:{
				var fields = t.fields();
				for( var k of fields.keys() ){
					indexSetAux( fields.get(k), c, set );
				}
				return;
			}
			case types.StackedType:{
				indexSetAux( t.left(), c, set );
				indexSetAux( t.right(), c, set );
				return;
			}
			case types.CapabilityType:{
				indexSetAux( t.location(), c, set );
				indexSetAux( t.value(), c, set );
				return;
			}
			case types.AlternativeType:
			case types.IntersectionType:
			case types.StarType:
			case types.TupleType: {
				var ts = t.inner();
				for( var i=0 ; i<ts.length ; ++i ){
					indexSetAux( ts[i], c, set );
				}
				return;
			}
			case types.SumType:{
				var ts = t.tags();
				for( var k of ts.keys() ){
					indexSetAux( ts.get(k), c, set );
				}
				return;
			}
			case types.ForallType:		
			case types.ExistsType:{
				if( t.bound() !== null ){
					indexSetAux( t.bound(), c, set );
				}
				indexSetAux( t.inner(), c+1, set );
				return;
			}
			case types.TypeVariable:
			case types.LocationVariable:{
				if( t.index() >= c ){
					set.add( t.index() - c );
				}
				return;
			}
			case types.DefinitionType: {				
				var ts = t.args();
				for( var i=0 ; i<ts.length ; ++i ){
					indexSetAux( ts[i], c, set );
				}
				return;
			}
//			case types.NoneType:
//			case types.PrimitiveType:
			default:
				return;
		}
	};


	var isProtocol = function( t, trail ){
		switch( t.type ){
			case types.NoneType:
				return true;
			case types.RelyType:
				return true;
			case types.ExistsType:
				return isProtocol( t.inner(), trail );
			case types.AlternativeType:
			case types.IntersectionType:
			case types.StarType: {
				var ts = t.inner();
				for( var i=0; i<ts.length; ++i ){
					if( !isProtocol( ts[i], trail ) )
						return false;
				}
				return true;
			}
			case types.DefinitionType:{
				// lazy use of 'trail' since it should not be needed.
				if( trail === undefined ){
					trail = new Set();
				}
				var key = t.toString(true);
				if( trail.has(key) )
					return true; // assume isProtocol elsewhere
				trail.add(key);
				return isProtocol( unfold(t), trail );
			}
			default:
				return false;
		}
	};

	exports.shift = shift;
	exports.unify = unify;
	exports.unfold = unfold;
	exports.unfoldDefinition = unfoldDefinition;
	exports.substitution = substitution;
	exports.subtype = subtype;
	exports.equals = equals;
	exports.isFree = isFree;
	exports.isProtocol = isProtocol;
	exports.indexSet = indexSet;

	return exports;

})( TypeChecker ); // required globals

