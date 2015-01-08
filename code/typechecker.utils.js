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
	}

	// returns null when no SINGLE/UNIQUE match found, else type
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

			// assume no match on cycles
			if( trail.has(key) )
				return null;

			trail.add(key);
			t = deft ? unfold(t) : t;
			a = defa ? unfold(a) : a;

			return unifyAux( x, t, a, trail );
		}

		// no match a this level, attempt further down.

		if( t.type !== a.type )
			return null; // failed to match

		var tmp = null;
		// returns whether it should abort, leaves result in 'tmp'
		var aux = function(v){
			if( tmp === null ){
				tmp = v;
				return true;
			}
			// else must be equals
			return v === null || equals( tmp, v );
		}

		switch( t.type ){
			case types.FunctionType: {
				if( !aux( unifyAux( x, t.argument(), a.argument(), trail ) )||
					!aux( unifyAux( x, t.body(), a.body(), trail ) ) )
					return null;
				return tmp;
			}

			case types.BangType:
				return unifyAux( x, t.inner(), a.inner(), trail );

			case types.RelyType:
			case types.GuaranteeType: {
				if( !aux( unifyAux( x, t.rely(), a.rely(), trail ) ) ||
					!aux( unifyAux( x, t.guarantee(), a.guarantee(), trail ) ) )
					return null;
				return tmp;
			}

			case types.SumType:{
				var ts = t.tags();
				var as = a.tags();

				if( ts.length !== as.length )
					return null;

				for( var i in ts ){
					var tt = t.inner( ts[i] );
					var at = a.inner( as[i] );

					// missing tag in 'a'
					if( at === undefined || !aux( unifyAux( x, tt, at, trail ) ) )
						return null;
				}

				return tmp;
			}

			case types.AlternativeType:
			case types.IntersectionType:
			case types.StarType: 
//FIXME: the order only matters on TupleTypes, not on the above.
//FIXME: A * B * C could be matched as X * C, etc.
			case types.TupleType: {
				var ts = t.inner();
				var as = a.inner();

				if( ts.length !== as.length )
					return null;

				for( var i=0; i<ts.length; ++i ){
					if( !aux( unifyAux( x, ts[i], as[i], trail ) ) )
						return null;
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
					return null;
				
				// going inside an existential, we must shift 'x' index
				var xi = shift1(x,0);

				// these remain intentionally unchanged
				var ti = t.inner();
				var ai = a.inner();

				if( !aux( unifyAux( xi, ti, ai, trail ) ) )
					return null;

				return tmp;
			}

			case types.ReferenceType: {
				return unifyAux( x, t.location(), a.location(), trail );
			}

			case types.StackedType: {
				if( !aux( unifyAux( x, t.left(), a.left(), trail ) ) ||
					!aux( unifyAux( x, t.right(), a.right(), trail ) ) )
					return null;
				return tmp;
			}

			case types.CapabilityType: {
				if( !aux( unifyAux( x, t.location(), a.location(), trail ) ) ||
					!aux( unifyAux( x, t.value(), a.value(), trail ) ) )
					return null;
				return tmp;
			}

			case types.RecordType: {
				var ts = t.getFields();
				var as = a.getFields();

				if( ts.length !== as.length )
					return null;

				for( var i in ts ){
					var ti = ts[i];
					var ai = as[i];

					// missing tag in 'a'
					if( ai === undefined || !aux( unifyAux( x, ti, ai, trail ) ) )
						return null;
				}

				return tmp;
			}

			case types.LocationVariable:
			case types.TypeVariable:
			case types.PrimitiveType:
			case types.NoneType:
			case types.TopType:
				return null;

			default:
				error( "@unifyAux: Not expecting " +t.type );
		}
	}


	// shifts indexes of free variables in 't' by 1.
	// t -> type
	// c -> cutoff index
	var shift1 = function( t, c ){

		switch ( t.type ){

			case types.FunctionType:
				return new FunctionType(
						shift1( t.argument(), c ),
						shift1( t.body(), c ) );

			case types.BangType:
				return new BangType( shift1( t.inner(), c ) );

			case types.RelyType: 
				return new RelyType(
							shift1( t.rely(), c ),
							shift1( t.guarantee(), c ) );

			case types.GuaranteeType:
				return new GuaranteeType(
							shift1( t.guarantee(), c ),
							shift1( t.rely(), c ) );

			case types.SumType:{
				var sum = new SumType();
				var tags = t.tags();
				for( var i in tags )
					sum.add( tags[i], shift1( t.inner(tags[i]), c ) );
				return sum;
			}

			case types.AlternativeType:
			case types.IntersectionType:
			case types.StarType: 
			case types.TupleType: {
				var star = new t.constructor();
				var inners = t.inner();
				for( var i=0;i<inners.length;++i ){
					star.add( shift1( rec(inners[i]), c ) );
				}	
				return star;
			}

			case types.ExistsType:
			case types.ForallType:
				// calls appropriate constructor function
				return new t.constructor( t.id(), shift1( t.inner(), c+1 ), t.bound() );

			case types.ReferenceType:
				return new ReferenceType( shift1( t.location(), c ) );
			
			case types.StackedType:
				return new StackedType( shift1( t.left(), c ), shift1( t.right(), c ) );

			case types.CapabilityType:
				return new CapabilityType( shift1( t.location(), c ), shift1( t.value(), c ) );
			
			case types.RecordType: {
				var r = new RecordType();
				var fs = t.getFields();
				for( var i in fs )
					r.add( i, shift1( fs[i], c ) );
				return r;
			}

			case types.DefinitionType: {
				var fs = t.args();
				var tmp = [];
				for( var i in fs )
					tmp = tmp.concat( shift1( fs[i], c ) );
				return new DefinitionType(t.definition(),tmp,t.getTypeDef());
			}

			case types.LocationVariable:
			case types.TypeVariable:
				if( t.index() < c )
					return t;
				return t.copy( t.index()+1 );

			case types.PrimitiveType:
			case types.NoneType:
			case types.TopType:
				return t;
			default:
				error( "@shift1: Not expecting " +t.type );
		}
	}

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
	}

	var equalsAux = function( t1, t2, trail ){

		if( t1 === t2 )
			return true;

		// if mismatch on DefinitionType
		var def1 = t1.type === types.DefinitionType;
		var def2 = t2.type === types.DefinitionType;

		if( def1 || def2 ){
			var key = t1.toString(true) + t2.toString(true);

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
				// note that it is an array of tags (strings)
				if( t1s.length !== t2s.length )
					return false;
				for( var i=0; i<t1s.length; ++i ){
					if( t2s.indexOf(t1s[i])===-1 ||
						!equalsAux( t1.inner(t1s[i]), t2.inner(t1s[i]), trail ) )
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
				var t1s = t1.getFields();
				var t2s = t2.getFields();
				if( Object.keys(t1s).length !== Object.keys(t2s).length )
					return false;
				for( var i in t2s )
					if( !t1s.hasOwnProperty(i) || 
						!equalsAux( t1s[i], t2s[i], trail ) )
						return false;
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
			var tags = t.tags();
			for( var i in tags )
				sum.add( tags[i], rec(t.inner(tags[i])) );
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
			// updates the indexes (see Types and Programming Languages, Chapter 6)
			var _to = shift1(to,0);
			var _from = shift1(from,0);

			var nvar = t.id();
			var ninner = t.inner();
			var nbound = t.bound();

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
			var fs = t.getFields();
			for( var i in fs )
				r.add( i, rec(fs[i]) );
			return r;
		}
		case types.DefinitionType: {
			var fs = t.args();
			var tmp = [];
			for( var i in fs )
				tmp = tmp.concat( rec(fs[i]) );
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
	 var subtype = function( t1, t2, env ){
	 	return subtypeAux( t1, t2, env, new Set() );
	 }

	var subtypeAux = function( t1 , t2, env, trail ){

		if( t1 === t2 || equals(t1,t2) ) // A <: A
			return true;
		
		// if mismatch on DefinitionType
		var def1 = t1.type === types.DefinitionType;
		var def2 = t2.type === types.DefinitionType;

		if( def1 || def2 ){
			var key = t1.toString(true) + t2.toString(true);

			// algorithm based on "Subtyping Recursive Types".
			if( trail.has(key) )
				return true;

			trail.add(key);
			t1 = def1 ? unfold(t1) : t1;
			t2 = def2 ? unfold(t2) : t2;

			return subtypeAux( t1, t2, env, trail );
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
			return subtypeAux( t1.inner(), t2, env, trail );
	
		// types that can be "banged"
		if ( t2.type === types.BangType &&
			( t1.type === types.ReferenceType
			|| t1.type === types.PrimitiveType
			|| ( t1.type === types.RecordType && t1.isEmpty() ) ) )
			return subtypeAux( t1, t2.inner(), env, trail );
			
		// "ref" t1: (ref p) <: !(ref p)
		if ( t1.type === types.ReferenceType && t2.type === types.BangType )
			return subtypeAux( t1, t2.inner(), env, trail );
		
		if( t1.type !== types.AlternativeType && t2.type === types.AlternativeType ){
			// only requirement is that t1 is one of t2's alternative
			var i2s = t2.inner();
			for(var j=0;j<i2s.length;++j) {
				if( subtypeAux( t1, i2s[j], env, trail ) ){
					return true;
				}
			}
			return false;
		}
		
		if( t1.type === types.IntersectionType && t2.type !== types.IntersectionType ){
			// one of t1s alts is t2
			var i1s = t1.inner();
			for(var j=0;j<i1s.length;++j) {
				if( subtypeAux( i1s[j], t2, env, trail ) ){
					return true;
				}
			}
			return false;
		}

		if( t2.type === types.ExistsType && t1.type !== types.ExistsType ){
			// if found unification and it obeys bound, successed.
			var u = unify( t2.id(), t2.inner(), t1 );
			if( u === null )
				return false;
			var b = t2.bound();
			return b === null || subtypeAux( u, b, env, trail );
		}
		
		if( t1.type === types.ForallType && t2.type !== types.ForallType ){
			var u = unify( t1.id(), t1.inner(), t2 );
			if( u === null )
				return false;
			var b = t1.bound();
			return b === null || subtypeAux( u, b, env, trail );
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
				return subtypeAux( t1.inner(), t2.inner(), env, trail );
			case types.ReferenceType:
				return subtypeAux( t1.location(), t2.location(), env, trail );
			case types.RelyType: {
				return subtypeAux( t1.rely(), t2.rely(), env, trail ) &&
					subtypeAux( t1.guarantee(), t2.guarantee(), env, trail );
			}
			case types.GuaranteeType: {
				return subtypeAux( t1.guarantee(), t2.guarantee(), env, trail ) &&
					subtypeAux( t1.rely(), t2.rely(), env, trail );
			}
			case types.FunctionType:
				return subtypeAux( t2.argument(), t1.argument(), env, trail )
					&& subtypeAux( t1.body(), t2.body(), env, trail );
			case types.RecordType:{
				if( !t1.isEmpty() && t2.isEmpty() )
					return false;

				// all fields of t2 must be in t1
				var t1fields = t1.getFields();
				var t2fields = t2.getFields();				
				for( var i in t2fields ){
					if( !t1fields.hasOwnProperty(i) ||
						!subtypeAux( t1fields[i], t2fields[i], env, trail ) ){
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
					if( !subtypeAux( t1s[i], t2s[i], env, trail ) )
						return false;
				return true;
			}

			case types.StackedType:
				return subtypeAux( t1.left(), t2.left(), env, trail ) &&
					subtypeAux( t1.right(), t2.right(), env, trail );

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
						if( subtypeAux( curr, tmp, env, trail ) ){
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
						if( subtypeAux( curr, tmp, env, trail ) ){
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
						if( subtypeAux( curr, tmp, env, trail ) ){
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
				for( var i in i1s ){
					var j = t2.inner(i1s[i]);
					if( j === undefined || // if tag is missing, or
						!subtypeAux( t1.inner(i1s[i]), j, env, trail ) )
						return false;
				}
				return true;
			}
			case types.CapabilityType:
				return subtypeAux( t1.location(), t2.location(), env, trail ) &&
					subtypeAux( t1.value(), t2.value(), env, trail );
				
			case types.ForallType:		
			case types.ExistsType:{
				
				if( t1.id().type !== t2.id().type )
					return false;
				if( !equals( t1.bound(), t2.bound() ) )
					return false;

				var i = t1.id();
				// name does not matter here since we will be fetching by depth.
				var e = env.newScope( i.name(), i, t1.bound() );
				
				return subtypeAux( t1.inner(), t2.inner(), e, trail );
			}

			case types.TypeVariable:
			case types.LocationVariable:
				return t1.index() === t2.index();

			default:
				error( "@subtype: Not expecting " +t1.type );
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
	}	
	
	var unfoldDefinition = function(d){
		if( d.type !== types.DefinitionType )
			return d;
		var t = d.getDefinition();
		var args = d.args();
		var pars = d.getParams();
		// type definitions will only replace Type or Location Variables, we
		// can use the simpler kind of substitution.
		for(var i=0;i<args.length;++i){
			t = substitution(t,pars[i],args[i]);
		}
		return t;
	}

	exports.unfold = unfold;
	exports.substitution = substitution;
	exports.subtype = subtype;
	exports.equals = equals;

	return exports;

})( TypeChecker ); // required globals

