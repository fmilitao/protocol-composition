// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

/**
 * INCLUDE parser.js
 * INCLUDE typechecker.utils.js
 * 	AST : AST.kinds, for all AST case analysis needs.
 *  TypeChecker : for error/assert functions.
 */

var TypeChecker = (function(AST,exports){

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

	const Environment = exports.Environment;

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

		/* FIXME --- simplify code:
		var tmp = null;
		var aux = function(v){
			if( tmp === null ){
				tmp = v;
				return true;
			}
			// else must be equals
			return v !== null !equals( tmp, v );
		} */

		switch( t.type ){
			case types.FunctionType: {
				var arg = unifyAux( x, t.argument(), a.argument(), trail );
				var bdy = unifyAux( x, t.body(), a.body(), trail );

				// if both have a match but it is not same type, fail
				if( arg!==null && bdy!==null && !equals( arg, bdy ) )
					return null;

				// if not null, just returns null also.
				return arg===null ? bdy : arg;
			}

			case types.BangType:
				return unifyAux( x, t.inner(), a.inner(), trail );

			case types.RelyType:
			case types.GuaranteeType: {
				var r = unifyAux( x, t.rely(), a.rely(), trail );
				var g = unifyAux( x, t.guarantee(), a.guarantee(), trail );
				
				if( r!==null && g!==null && !equals( r, g ) )
					return null;

				return r===null ? g : r ;
			}

			case types.SumType:{
				var ts = t.tags();
				var as = a.tags();

				if( ts.length !== as.length )
					return null;

				var tmp = null;
				for( var i in ts ){
					var ti = ts[i];
					var ai = as[i];
					var tt = t.inner(ti);
					var at = a.inner(ai);

					// missing tag in 'a'
					if( at === undefined )
						return null;

					var tmpi = unifyAux( x, tt, at, trail );

					if( tmp === null ){
						tmp = tmpi;
					} else {
						// not all equals, then fail
						if( tmpi !== null && !equals( tmp, tmpi ) )
							return null;
					}
				}

				return tmp;
			}

			case types.AlternativeType:
			case types.IntersectionType:
			case types.StarType: 
//FIXME: the order only matters on TupleTypes, not on the above.
			case types.TupleType: {
				var ts = t.inner();
				var as = a.inner();

				if( ts.length !== as.length )
					return null;

				var tmp = null;
				for( var i=0; i<ts.length; ++i ){
					var ti = ts[i];
					var ai = as[i];

					var tmpi = unifyAux( x, ti, ai, trail );

					if( tmp === null ){
						tmp = tmpi;
					} else {
						// not all equals, then fail
						if( tmpi !== null && !equals( tmp, tmpi ) )
							return null;
					}
				}

				return tmp;
			}

			case types.ExistsType:
			case types.ForallType: {
//FIXME does unify also operate over *.bound() ??
				
				// going inside an existential, we must shift 'x' index
				var xi = shift1(x,0);

				// these remain intentionally unchanged
				var ti = t.inner();
				var ai = a.inner();

				return unifyAux( xi, ti, ai, trail );
			}

			case types.ReferenceType: {
				return unifyAux( x, t.location(), a.location(), trail );
			}

			case types.StackedType: {
				var l = unifyAux( x, t.left(), a.left(), trail );
				var r = unifyAux( x, t.right(), a.right(), trail );

				// if both have a match but it is not same type, fail
				if( l!==null && r!==null && !equals( l, r ) )
					return null;

				// if not null, just returns null also.
				return l===null ? r : l;
			}

			case types.CapabilityType: {
				var l = unifyAux( x, t.location(), a.location(), trail );
				var r = unifyAux( x, t.value(), a.value(), trail );

				// if both have a match but it is not same type, fail
				if( l!==null && r!==null && !equals( l, r ) )
					return null;

				// if not null, just returns null also.
				return l===null ? r : l;
			}

			case types.RecordType: {
				var ts = t.getFields();
				var as = a.getFields();

				if( ts.length !== as.length )
					return null;

				var tmp = null;
				for( var i in ts ){
					var ti = ts[i];
					var ai = as[i];

					// missing tag in 'a'
					if( ai === undefined )
						return null;

					var tmpi = unifyAux( x, ti, ai, trail );

					if( tmp === null ){
						tmp = tmpi;
					} else {
						// not all equals, then fail
						if( tmpi !== null && !equals( tmp, tmpi ) )
							return null;
					}
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
				return new DefinitionType(t.definition(),tmp);
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
			return new DefinitionType(t.definition(),tmp);
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
	
	//
	// EQUALS and SUBTYPING
	//	
	
	/**
	 * Subtyping two types.
	 * @param {Type} t1
	 * @param {Type} t2
	 * @return {Boolean} true if t1 <: t2 (if t1 can be used as t2).
	 */
	 var subtype = function( t1, t2 ){
	 	return subtypeAux( t1, t2, new Set() );
	 }

	var subtypeAux = function( t1 , t2, trail ){

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

			return subtypeAux( t1, t2, trail );
		}

		if( t2.type === types.TopType && t1.type !== types.LocationVariable )
			return true;

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
			// if found unification and it obeys bound, successed.
			var u = unify( t2.id(), t2.inner(), t1 );
			if( u !== null && subtype( u, t2.bound() ) )
				return true;
		}
		
		if( t1.type === types.ForallType && t2.type !== types.ForallType ){
			var u = unify( t1.id(), t1.inner(), t2 );
			if( u !== null && subtype( u, t1.bound() ) )
				return true;
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
			case types.RelyType: {
				return subtypeAux( t1.rely(), t2.rely(), trail ) &&
					subtypeAux( t1.guarantee(), t2.guarantee(), trail );
			}
			case types.GuaranteeType: {
				return subtypeAux( t1.guarantee(), t2.guarantee(), trail ) &&
					subtypeAux( t1.rely(), t2.rely(), trail );
			}
			case types.FunctionType:
				return subtypeAux( t2.argument(), t1.argument(), trail )
					&& subtypeAux( t1.body(), t2.body(), trail );
			case types.RecordType:{
				if( !t1.isEmpty() && t2.isEmpty() )
					return false;

				// all fields of t2 must be in t1
				var t1fields = t1.getFields();
				var t2fields = t2.getFields();				
				for( var i in t2fields ){
					if( !t1fields.hasOwnProperty(i) ||
						!subtypeAux( t1fields[i], t2fields[i], trail ) ){
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
				for( var i in i1s ){
					var j = t2.inner(i1s[i]);
					if( j === undefined || // if tag is missing, or
						!subtypeAux( t1.inner(i1s[i]), j, trail ) )
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

				return equals( t1.bound(), t2.bound() ) &&
					subtypeAux( t1.inner(), t2.inner(), trail );
			}

			case types.TypeVariable:
			case types.LocationVariable:
				return t1.index() === t2.index();

			default:
				error( "@subtype: Not expecting " +t1.type );
		}

	};
	
	// TypeVariables must be upper cased.
	var isTypeVariableName = function(n){
		return n[0] === n[0].toUpperCase();
	}
	
	//
	// TYPE CHECKER
	//

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
		if( d.type !== types.DefinitionType || typedef.isInRecDefs() )
			return d;
		var t = typedef.getDefinition(d.definition());
		var args = d.args();
		var pars = typedef.getType(d.definition());
		// type definitions will only replace Type or Location Variables, we
		// can use the simpler kind of substitution.
		for(var i=0;i<args.length;++i){
			t = substitution(t,pars[i],args[i]);
		}
		return t;
	}
	
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

	// this wrapper function allows us to inspect the type and envs
	// of some node, while leaving the checker mostly clean.
	var check = function(ast,env) {
		var info = { ast : ast, env : env.clone() };
		type_info.push( info );
		var res = check_inner( ast, env );
		info.res = res;
		if( ast.kind === AST.SHARE ){
			info.conformance = hack_info;
		}
		return res;
	};

	/**
	 * @param {AST} ast, tree to check
	 * @param {Environment} env, typing environment at beginning
	 * @return either the type checked for 'ast' or throws a type error with
	 * 	what failed to type check.
	 */
	var setupAST = function( kind ) {
		
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
				var tmp = env.getType( label );
				// if label matches type in environment, but we only allow
				// access to type variables and location variables using this
				// AST.kind --- all other uses are assumed to be recursives.
				if( tmp !== undefined &&
					( tmp.type === types.TypeVariable ||
					  tmp.type === types.LocationVariable ) ){
						return tmp.copy( env.getTypeDepth(label) );
				}
				
				// look for type definitions
				var lookup_args = typedef.getType(label);

				// if found something, that is not yet defined
				if( lookup_args !== undefined &&
						lookup_args.length === 0 )
					return new DefinitionType(label, new Array(0));
		
				assert( 'Unknown type '+label, ast);
			};
			
			case AST.DEFINITION_TYPE:
			return function( ast, env ){
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
				
				return new DefinitionType(id,arguments);
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
				if( guarantee.type !== types.GuaranteeType ){
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
				var loc = env.getType( id );
				
				assert( (loc !== undefined && loc.type === types.LocationVariable) ||
					('Unknow Location Variable '+id), ast );
				
				return new ReferenceType( loc.copy( env.getTypeDepth( id ) ) );
			};
			
			case AST.EXISTS_TYPE: 
			return function( ast, env ){
				var id = ast.id;
				var e = env.newScope();
				
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
				
				e.setType( id, variable );
				if( bound !== null )
					e.setBound( id, bound );

				var type = check( ast.exp, e );

				return new ExistsType( variable, type, bound );
			};
			
			case AST.FORALL:
			case AST.FORALL_TYPE: 
			return function( ast, env ){
				var id = ast.id;
				var e = env.newScope();
				
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

				e.setType( id, variable );
				if( bound !== null )
					e.setBound( id, bound );

				var type = check( ast.exp, e );

				return new ForallType( variable, type, bound );
			};
						
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
	
	var visitor = {};
	// setup visitors
	for( var i in AST ){
		error( !visitor.hasOwnProperty(i) ||
				( 'Error @visitor, duplication: '+i ) );
		// find witch function to call on each AST kind of node
		visitor[i] = setupAST(i);
	}
	
	var check_inner = function( ast, env ){
		if( !visitor.hasOwnProperty( ast.kind ) ){
			error( 'Not expecting '+ast.kind );
		}
		return (visitor[ast.kind])( ast, env );
	}
		
	var TypeDefinition = function(){
		var inRecDef;
		var typedefs;
		var typedefs_args;

		// these 3 methods must be used to avoid attempts at resoving recursive
		// definitions before they are all inserted/defined.
		this.beginRecDefs = function(){ inRecDef = true; };
		this.endRecDefs = function(){ inRecDef = false; };
		this.isInRecDefs = function(){ return inRecDef; }; //FIXME is this still necessary?
		
		this.addType = function(name,array){
			if( typedefs_args.hasOwnProperty(name) )
				return false;
			typedefs_args[name] = array;
			return true;
		};
		this.addDefinition = function(name,definition){
			if( typedefs.hasOwnProperty(name) )
				return false;
			typedefs[name] = definition;
			return true;
		};
		this.getType = function(name){
			return typedefs_args[name];
		};
		this.getDefinition = function(name){
			return typedefs[name];
		};
		this.reset = function(){
			inRecDef = false;
			typedefs = {};
			typedefs_args = {};
		};

		this.reset();
	};

	var type_info;
	var typedef = new TypeDefinition();

	// exporting these functions to facilitate testing.	
	exports.subtype = subtype;
	exports.equals = equals;
	exports.typedef = typedef;
	exports.checkProtocolConformance = checkProtocolConformance;
	
	exports.check = function(ast,typeinfo,loader){
		// stats gathering
		var start = new Date().getTime();
		type_info = [];

		try{
			error( (ast.kind === AST.PROGRAM) || 'Unexpected AST node' );
				
			// reset typechecke's state.
			typedef.reset();
			var env = new Environment(null);
				
			if( ast.typedefs !== null ){

				// first phase - extract all argument definitions, note that
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
				
				// must avoid attempting to unfold what is not yet definied.
				typedef.beginRecDefs();

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
				
				// ok to allow unfoldings
				typedef.endRecDefs();

				//check for bottom types.
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

			var exps = ast.exp;
			for( var i=0; i<exps.length; ++i ){
				check( exps[i], env );
			}
			return NoneType;
		} finally {
			if( typeinfo ){
				typeinfo.diff = (new Date().getTime())-start;
				typeinfo.info = type_info; 
			}
		}

	};
	return exports;
})( AST.kinds, TypeChecker ); // required globals

