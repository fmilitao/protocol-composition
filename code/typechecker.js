// Copyright (C) 2014 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

/**
 * REQUIRED Global variables (all declared in parser.js):
 * 	- AST.kinds, for all AST case analysis needs.
 *  - assertf, for error handling/flagging.
 */

var TypeChecker = (function(AST,assertF){

	var exports = {};
	
	/*
	 * WARNING - Usage Notes:
	 * The following two function smake use of a side-effect when evaluating
	 * an OR such that A || B will only compute B if A is NOT true. Therefore
	 * the following functions make use of that assumption on their argument
	 * such that if the argument is true, then the function does nothing, else
	 * it throws the respective error with the argument which should be a string
	 * so that it can be used as:
	 *		assert( CONDITION || EXPENSIVE_ERROR_MSG , AST );
	 * and not compute EXPENSIVE_ERROR_MSG unless CONDITION is false.
	 */
	
	// yields true or string on error
	var assert = function( msg, ast ){
		// if a boolean and true
		if( typeof(msg) === 'boolean' && msg )
			return;
		assertF( 'Type error', false, msg, ast );
	}
	
	// these are program assertions and should never be seen by users
	// unless there is a major malfunction in the code (bug...)
	var error = function(msg){
		// if a boolean and true
		if( typeof(msg) === 'boolean' && msg )
			return;
		// else it should be a string with the type error
		assertF( 'Bug Alert', false, msg, undefined ); // undefined blamed 'ast'
	}

	//
	// TYPES
	//
	
	var types = {}; // types enumeration, useful for case analysis
	var fct = {}; // types factory

	var newType = function( type, constructor ){
		error( ( !types.hasOwnProperty(type) && !fct.hasOwnProperty(type) )
			|| ( '@newType: already exists: '+type ) );
		
		// default stuff for that particular type
		constructor.prototype.type = type;

		// later it may be useful to change away from strings, but for now
		// they are very useful when debugging problems.
		types[type] = type;
		fct[type] = constructor;
		return constructor;
	};
	
	// Note: all constructors are labelled to make heap profiling easier.
	
	var FunctionType = newType('FunctionType',
		function FunctionType( argument, body ) {
			this.argument = function(){ return argument; }
			this.body = function(){ return body; }
		}
	);
	
	var BangType = newType('BangType',
		function BangType( inner ) {
			this.inner = function(){ return inner; }
		}
	);
	
	var SumType = newType('SumType',
		function SumType() {
			var tags = {};
			this.add = function( tag, inner ){
				if ( tags.hasOwnProperty(tag) )
					return undefined; // already exists!
				tags[tag] = inner;
				return true;
			}
			this.tags = function(){ return Object.keys(tags); }
			this.inner = function(tag){ return tags[tag]; }
		}
	);
	
	var StarType = newType('StarType',
		function StarType() {
			var types = [];
			this.add = function( inner ){
				types.push(inner);
				return true;
			}
			this.inner = function(){ return types; }
		}
	);
	
	var AlternativeType = newType('AlternativeType',
		function AlternativeType() {
			var alts = [];
			this.add = function( inner ){
				alts.push(inner);
				return true;
			}
			this.inner = function(){ return alts; }
		}
	);
	
	var IntersectionType = newType('IntersectionType',
		function IntersectionType() {
			var alts = [];
			this.add = function( inner ){
				alts.push(inner);
				return true;
			}
			this.inner = function(){ return alts; }
		}
	);
	
	var ForallType = newType('ForallType',
		function ForallType( id, inner ) {
			this.id = function(){ return id; }
			this.inner = function(){ return inner; }
		}
	);
	
	var ExistsType = newType('ExistsType',
		function ExistsType( id, inner ) {
			this.id = function(){ return id; }
			this.inner = function(){ return inner; }
		}
	);
	
	var RecordType = newType('RecordType',
		function RecordType(){
			var fields = {};
			this.add = function(id, type) {
				if ( fields.hasOwnProperty(id) ){
					return undefined;
				}
				fields[id] = type;
				return true;
			}
			this.select = function(id) {
				if (fields.hasOwnProperty(id)) {
					return fields[id];
				} else {
					return undefined;
				}
			}
			this.isEmpty = function(){
				return Object.keys(fields).length===0;
			}
			this.getFields = function(){
				return fields;
			}
		}
	);
	
	var NoneType = newType('NoneType',
		function NoneType(){
			// intentionally empty	
		}
	);
	
	// singleton value for this type.
	NoneType = new NoneType();
	
	var TupleType = newType('TupleType',
		function TupleType(){
			var values = [];
			this.add = function(type) {
				values.push(type);
				return true;
			}
			this.getValues = function(){
				return values;
			}
		}
	);

	var ReferenceType = newType('ReferenceType',
		function ReferenceType( location ){
			this.location = function(){ return location; }
		}
	);
	
	var StackedType = newType('StackedType',
		function StackedType( left, right ){
			this.left = function(){ return left; }
			this.right = function(){ return right; }
		}
	);
	
	var CapabilityType = newType('CapabilityType',
		function CapabilityType( loc, val ){
			this.location = function(){ return loc; }
			this.value = function(){ return val; }
		}
	);
	
	var LocationVariable = newType('LocationVariable',
		function LocationVariable( name ){
			var n = name === null ? 't<sub>'+(unique_counter++)+'</sub>' : name;
			
			this.name = function(){ return n; }
			this.clone = function( n ){ return new LocationVariable(n); }
		}
	);
	
	var TypeVariable = newType('TypeVariable',
		function TypeVariable( name ){
			var n = name === null ? 'T<sub>'+(unique_counter++)+'</sub>' : name;
			
			this.name = function(){ return n; }
			this.clone = function( n ){ return new TypeVariable(n); }
		}
	);
	
	var PrimitiveType = newType('PrimitiveType',
		function PrimitiveType( name ){
			this.name = function(){ return name; }
		}
	);
	
	var RelyType = newType('RelyType',
		function RelyType( rely, guarantee ){
			this.rely = function(){ return rely; }
			this.guarantee = function(){ return guarantee; }
		}
	);
	
	var GuaranteeType = newType('GuaranteeType',
		function GuaranteeType( guarantee, rely ){
			this.rely = function(){ return rely; }
			this.guarantee = function(){ return guarantee; }
		}
	);
	
	var DefinitionType = newType('DefinitionType',
		function DefinitionType( definition_name, arg ){
			this.definition = function(){ return definition_name; }
			this.args = function(){ return arg; }
		}
	);
	
	exports.types = types;
	exports.factory = fct;
	
	// append toString method to types
	(function(){
		// defines which types get wrapping parenthesis
		var _wrap = function(t){
			if( t.type === types.ReferenceType ||
				t.type === types.FunctionType ||
				t.type === types.StackedType ||
				t.type === types.StarType || 
				t.type === types.AlternativeType ||
				t.type === types.SumType ){
					return '('+t.toString()+')';
				}
			return t.toString();
		};
		var _add = function(t,fun){
			error( !fct[t].hasOwnProperty('toString') || ("Duplicated " +k) );
			fct[t].prototype.toString = fun;
		};
		
		_add( types.FunctionType, function(){
			return _wrap( this.argument() )+" -o "+_wrap( this.body() );
		} );
		
		_add( types.BangType, function(){
			return "!"+_wrap( this.inner() );
		} );

		_add( types.RelyType, function(){
			return _wrap( this.rely() )+' => '+_wrap( this.guarantee() );
		} );

		_add( types.GuaranteeType, function(){
			return _wrap( this.guarantee() )+' ; '+_wrap( this.rely() );
		} );
		
		_add( types.SumType, function(){
			var tags = this.tags();
			var res = [];
			for( var i in tags ){
				res.push( tags[i]+'#'+_wrap( this.inner(tags[i]) ) ); 
			}	
			return res.join('+');
		} );

		_add( types.StarType, function(){
			var inners = this.inner();
			var res = [];
			for( var i=0; i<inners.length; ++i )
				res.push( _wrap( inners[i] ) ); 
			return res.join(' * ');
		} );
		
		_add( types.AlternativeType, function(){
			var inners = this.inner();
			var res = [];
			for( var i=0; i<inners.length; ++i )
				res.push( _wrap( inners[i] ) ); 
			return res.join(' (+) ');
		} );
		
		_add( types.IntersectionType, function(){
			var inners = this.inner();
			var res = [];
			for( var i=0; i<inners.length; ++i )
				res.push( _wrap( inners[i] ) ); 
			return res.join(' & ');
		} );
		
		_add( types.ExistsType, function(){
			return 'exists '+this.id().name()+'.'+_wrap( this.inner() );
		} );
		
		_add( types.ForallType, function(){
			return 'forall '+this.id().name()+'.('+_wrap( this.inner() );
		} );
		
		_add( types.ReferenceType, function(){
			return "ref "+this.location().name();
		} );
		
		_add( types.CapabilityType, function(){
			return 'rw '+this.location().name()+' '+_wrap( this.value() );			
		} );
		
		_add( types.StackedType, function(){
			return _wrap( this.left() )+' :: '+_wrap( this.right() );
		} );
		
		_add( types.RecordType, function(){
			var res = [];
			var fields = this.getFields();
			for( var i in fields )
				res.push(i+": "+_wrap( fields[i]) );
			return "["+res.join()+"]";
		} );
		
		_add( types.TupleType, function(){
			return "["+this.getValues().join()+"]";
		} );
		
		_add( types.DefinitionType, function(){
			if( this.args().length > 0 )
				return _wrap( this.definition() )+'['+ this.args().join() +']';
			return _wrap( this.definition() );
		} );
		
		var tmp = function(){ return this.name(); };
		_add( types.LocationVariable, tmp );
		_add( types.TypeVariable, tmp );
		_add( types.PrimitiveType, tmp );
		
		_add( types.NoneType, function(){ return 'none'; });
		
	})();

	//
	// VISITORS
	//
	
	/**
	 * Searchs types 't' for location variable 'loc'. isFree if NOT present.
	 * @param {Type} t that is to be traversed
	 * @param {LocationVariable,TypeVariable} loc that is to be found
	 * @return {Boolean} true if location variableis NOT in type.
	 * Note that all variable names collide so that checking for 
	 * LocationVariable versus TypeVariable is not necessary.
	 */

	var isFree = (function(){
		var _visitor = {};
		var _add = function( k , fun ){
			error( !_visitor.hasOwnProperty(k) || ("Duplicated " +k) );
			_visitor[k] = fun;
		};
		
		_add( types.FunctionType, function(t,loc){
			return isFree( t.argument(), loc ) && isFree( t.body(), loc );
		});
		
		_add( types.BangType, function(t,loc){
			return isFree( t.inner(), loc );
		});
		
		_add( types.RelyType, function(t,loc){
			return isFree( t.rely(), loc ) && isFree( t.guarantee(), loc );
		});
		
		_add( types.GuaranteeType, function(t,loc){
			return isFree( t.guarantee(), loc ) && isFree( t.rely(), loc );
		});
 
		_add( types.SumType, function(t,loc){
			var tags = t.tags();
			for( var i in tags ){
				if( !isFree(t.inner(tags[i]),loc) )
					return false; 
			}	
			return true;
		});

		_add( types.ForallType, function(t,loc){
			if( t.id().name() === loc.name() ) {
				// the name is already bounded, so loc must be fresh
				// because it does not occur free inside t.inner()
				return true;
			}
			return isFree(t.id(),loc) && isFree(t.inner(),loc);
		});
		_add( types.ExistsType, _visitor[types.ForallType] ); //reuse definition

		_add( types.ReferenceType, function(t,loc){
			return isFree( t.location(), loc );
		});

		_add( types.StackedType, function(t,loc){
			return isFree( t.left(), loc ) && isFree( t.right(), loc );
		});
		
		_add( types.CapabilityType, function(t,loc){
			return isFree( t.location(), loc ) && isFree( t.value(), loc );
		});

		_add( types.RecordType, function(t,loc){
			var fs = t.getFields();
			for( var i in fs ){
				if( !isFree(fs[i],loc) )
					return false;
			}
			return true;
		});
		
		_add( types.AlternativeType, function(t,loc){
			var inners = t.inner();
			for( var i=0; i<inners.length; ++i )
				if( !isFree(inners[i],loc) )
					return false;
			return true;
		});
		_add( types.IntersectionType, _visitor[types.AlternativeType] );
		_add( types.StarType, _visitor[types.AlternativeType] ); //reuse def.
		
		_add( types.TupleType, function(t,loc){
			var vs = t.getValues();
			for( var i in vs ){
				if( !isFree(vs[i],loc) )
					return false;
			}
			return true;
		});
		
		_add( types.TypeVariable, function(t,loc){
			return t.name() !== loc.name();
		});
		_add( types.LocationVariable, _visitor[types.TypeVariable] ); //reuse def.
		
		_add( types.PrimitiveType, function(t,loc){ return true; });
		_add( types.NoneType, _visitor[types.PrimitiveType] );
		
		_add( types.DefinitionType, function(t,loc){
			// t.definition() is a name/identifer.
			var vs = t.args();
			for( var i in vs ){
				if( !isFree(vs[i],loc) )
					return false;
			}
			return true;
		});
		
		// the closure that uses the private _visitor
		return function (t,loc) {
			if( !_visitor.hasOwnProperty( t.type ) )
				error( "@isFree: Not expecting " +t.type );
			return _visitor[t.type](t,loc);
		};
	})();
	
	/**
	 * Substitutes in 'type' any occurances of 'from' to 'to'
	 * 		type[from/to] ('from' for 'to')
	 * @param {Type} type that is to be searched
	 * @param {Type} when 'from' is found, it is replaced with
	 * @param {LocationVariable,TypeVariable} 'to'
	 * @param {Function} equals function to compare types
	 * @return a *copy* of 'type' where all instances of 'from' have been
	 * 	replaced with 'to' (note that each to is the same and never
	 * 	cloned).
	 *  Note that it also RENAMES any bounded variable that colides with the
	 *  'from' name so that bounded names are never wrongly substituted.
	 */
	
	var substitutionF = function(t,from,to,eq){
		
		// for convenience...
		var rec = function(type){
			return substitutionF(type,from,to,eq);
		}
		
		if( eq(t,from) )
			return to;
			
		switch ( t.type ){
		case types.FunctionType:
			return new FunctionType( rec(t.argument()), rec(t.body()) );
		case types.BangType:
			return new BangType( rec(t.inner()) );
		case types.RelyType: {
			return new RelyType( rec(t.rely()), rec(t.guarantee()) );
		}
		case types.GuaranteeType: {
			return new GuaranteeType( rec(t.guarantee()), rec(t.rely()) );
		}
		case types.SumType:{
			var sum = new SumType();
			var tags = t.tags();
			for( var i in tags )
				sum.add( tags[i], rec(t.inner(tags[i])) );
			return sum;
		}
		case types.AlternativeType:{
			var star = new AlternativeType();
			var inners = t.inner();
			for( var i=0;i<inners.length;++i ){
				star.add( rec(inners[i]) ); 
			}	
			return star;
		}
		case types.IntersectionType:{
			var star = new IntersectionType();
			var inners = t.inner();
			for( var i=0;i<inners.length;++i ){
				star.add( rec(inners[i]) ); 
			}	
			return star;
		}
		case types.StarType:{
			var star = new StarType();
			var inners = t.inner();
			for( var i=0;i<inners.length;++i ){
				star.add( rec(inners[i]) ); 
			}	
			return star;
		}
		// CAPTURE AVOIDANCE in the following cases...
		// Renaming is needed to avoid capture of bounded variables.
		// We have two cases to consider:
		// 1. The variable to be renamed is the same as bounded var:
		// (exists t.A){t/X} "t for X" 
		// in this case, we are done renaming, since t is bounded inside A.
		// 2. The *to* name is the same the bounded var:
		// (exists t.A){g/t} "g for t"
		// in this case we must rename the location 't' to avoid capture
		// in the case when 'g' occurs in A.
		case types.ExistsType: 
		case types.ForallType: {
			if( ( from.type === types.LocationVariable ||
				  from.type === types.TypeVariable )
					&& t.id().name() === from.name() ){
				// 'from' is bounded, thus we are done. 
				return t;
			}
			
			var nvar = t.id();
			var ninner = t.inner();
			if( ( to.type === types.LocationVariable ||
				  to.type === types.TypeVariable )
					&& t.id().name() === to.name() ){
				// capture avoiding substitution 
				nvar = t.id().clone(null); // fresh loc/type-variable
				
				// must use simpler equals function to avoid unending cycles
				ninner = substitutionVarsOnly( t.inner(), t.id(), nvar );
			}
			
			// switch again to figure out what constructor to use.
			switch( t.type ){
				case types.ExistsType:
					return new ExistsType( nvar, rec(ninner) );
				case types.ForallType:
					return new ForallType( nvar, rec(ninner) );
				default:
					error( "@substitution: Not expecting " +t.type );
			}
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
		case types.TupleType: {
			var r = new TupleType();
			var fs = t.getValues();
			for( var i in fs )
				r.add( rec(fs[i]) );
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
			return t;

		default:
			error( "@substitution: Not expecting " +t.type );
		}
	};
	
	/*
	 * This is a "simpler" substitution where 'from' must either be a
	 * LocationVariable or a TypeVariable. This restriction simplifies the
	 * equality test since we are no longer attempting to match complete types
	 * and instead are just looking for TypeVariables or LocationVariables
	 */
	var substitutionVarsOnly = function(type,from,to){
		if( from.type !== types.LocationVariable && 
				from.type !== types.TypeVariable ){
			error( "@substitutionVarsOnly: not a Type/LocationVariable" );
		}
		return substitutionF(type,from,to,function(a,b){
			// same type and same name
			// WARNING: unstated assumption that 'a' is 'from'
			return a.type === b.type && a.name() === b.name();
		});
	};
	
	var substitution = function(t,from,to){
		return substitutionF(t,from,to,equals);
	};
	
	//
	// EQUALS and SUBTYPING
	//	

	/**
	 * Tests if types 'a' and 'b' are the same.
	 * Up to renaming of bounded variables, so that it renames existentials
	 * and foralls. Thus, returns true when they are structurally equal, even
	 * if their labels in existentials are of different strings values.
	 * @param {Type} a
	 * @param {Type} b
	 * @return {Boolean} if the types are equal up to renaming.
	 */
	var equals = function(t1,t2){

		// exactly the same
		if( t1 === t2 )
			return true;

		var def1 = t1.type === types.DefinitionType;
		var def2 = t2.type === types.DefinitionType;
		if( def1 ^ def2 ){
			if( def1 ){
				t1 = unAll(t1,false,true);
				// if unfolding worked
				if( t1.type !== types.DefinitionType ){
					return equals( t1, t2 );
				}
			}
			if( def2 ){
				t2 = unAll(t2,false,true);
				// if unfolding worked
				if( t2.type !== types.DefinitionType ){
					return equals( t1, t2 );
				}
			}
		}
		
		if( t1.type !== t2.type )
			return false;
			
		// assuming both same type
		switch ( t1.type ){
			case types.ForallType:		
			case types.ExistsType: {
				if( t1.id().type !== t2.id().type )
					return false;
					
				// if name mismatch, do "quick" substitution to make them match
				if( t1.id().name() !== t2.id().name() ){
					var tmp = substitutionVarsOnly(t2.inner(),t2.id(),t1.id());
					return equals( t1.inner(), tmp );
				}
		
				return equals( t1.inner(), t2.inner() );
			}
			case types.TypeVariable:
			case types.LocationVariable: {
				// note: same name for case of variables that are in scope
				// but not declared in the type (i.e. already opened)
				return  t1.name() === t2.name();
			}
			case types.FunctionType:
				return equals( t1.argument(), t2.argument() ) &&
					equals( t1.body(), t2.body() );
			case types.BangType:
				return equals( t1.inner(), t2.inner() );
			case types.RelyType: {
				var r1 = t1.rely();
				var r2 = t2.rely();
				var g1 = t1.guarantee();
				var g2 = t2.guarantee();

				if( !equals( r1, r2 ) )
					return false;
				
				try{
					// consider extensions
					var gg1 = g1.guarantee();
					var gg2 = g2.guarantee();
				
					if( gg1.type === types.NoneType && gg2.type !== types.NoneType ){
						var initial = gg2; // initial state
						var protocol = g2.rely();
						
						conformanceStateProtocol( initial, protocol, NoneType);
						return true;
					}
				}catch(e){
					return equals( g1, g2 );						
				}
				return equals( g1, g2 );
			}
			case types.GuaranteeType: {
				return equals( t1.guarantee(), t2.guarantee() ) &&
					equals( t1.rely(), t2.rely() );
			}
			case types.SumType: {
				var t1s = t1.tags();
				var t2s = t2.tags();
				// note that it is an array of tags (strings)
				if( t1s.length !== t2s.length )
					return false;
				for( var i=0; i<t1s.length; ++i ){
					if( t2s.indexOf(t1s[i])===-1 ||
						!equals( t1.inner(t1s[i]), t2.inner(t1s[i]) ) )
						return false;
				}
				return true;
			}
			case types.ReferenceType:
				return equals( t1.location(), t2.location() );
			case types.StackedType:
				return equals( t1.left(), t2.left() ) &&
					equals( t1.right(), t2.right() );
			case types.CapabilityType:
				return equals( t1.location(), t2.location() ) &&
					equals( t1.value(), t2.value() );
			case types.RecordType: {
				var t1s = t1.getFields();
				var t2s = t2.getFields();
				if( Object.keys(t1s).length !== Object.keys(t2s).length )
					return false;
				for( var i in t2s )
					if( !t1s.hasOwnProperty(i) || 
						!equals( t1s[i], t2s[i] ) )
						return false;
				return true;
			} 
			case types.TupleType: {
				var t1s = t1.getValues();
				var t2s = t2.getValues();
				if( t1s.length !== t2s.length )
					return false;
				for( var i=0;i<t1s.length;++i )
					if( !equals( t1s[i], t2s[i] ) )
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
						if( equals(curr,tmp) ){
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
			case types.DefinitionType:{
				if( t1.definition() !== t2.definition() )
					return false;
				
				var t1s = t1.args();
				var t2s = t2.args();
				if( t1s.length !== t2s.length )
					return false;
				for( var i=0;i<t1s.length;++i )
					if( !equals( t1s[i], t2s[i] ) )
						return false;
				return true;
			}
			default:
				error( "@equals: Not expecting " +t2.type );
			}
	};
	
	// for visited definitions
	var Table = function(){
		var visited = {};
		
		var keyF = function(a,b){
			return a < b ? a+b : b+a;
		};
		
		this.contains = function(a,b){
			return visited.hasOwnProperty( keyF(a,b) );
		}
		
		this.set = function(a,b,value){
			visited[keyF(a,b)] = value;
		}
		
		this.get = function(a,b){
			return visited[keyF(a,b)];
		}
	};
	
	/**
	 * Subtyping two types.
	 * @param {Type} t1
	 * @param {Type} t2
	 * @return {Boolean} true if t1 <: t2 (if t1 can be used as t2).
	 */
	var subtypeOf = function( t1 , t2 ){	
		if( t1 === t2 || equals(t1,t2) ) // A <: A
			return true;
		
		// if mismatch on DefinitionType
		var def1 = t1.type === types.DefinitionType;
		var def2 = t2.type === types.DefinitionType;
		if( def1 ^ def2 ){
			if( def1 ){
				t1 = unAll(t1,false,true);
				// if unfolding worked
				if( t1.type !== types.DefinitionType ){
					return subtypeOf( t1, t2 );
				}
			}
			if( def2 ){
				t2 = unAll(t2,false,true);
				// if unfolding worked
				if( t2.type !== types.DefinitionType ){
					return subtypeOf( t1, t2 );
				}
			}
		}

		// "pure to linear" - ( t1: !A ) <: ( t2: A )
		if ( t1.type === types.BangType && t2.type !== types.BangType )
			return subtypeOf( t1.inner(), t2 );
	
		// types that can be "banged"
		if ( t2.type === types.BangType &&
			( t1.type === types.ReferenceType
			|| t1.type === types.PrimitiveType
			|| ( t1.type === types.RecordType && t1.isEmpty() ) ) )
			return subtypeOf( t1, t2.inner() );
			
		// "ref" t1: (ref p) <: !(ref p)
		if ( t1.type === types.ReferenceType && t2.type === types.BangType )
			return subtypeOf( t1, t2.inner() );
		
		if( t1.type !== types.AlternativeType && t2.type === types.AlternativeType ){
			// only requirement is that t1 is one of t2's alternative
			var i2s = t2.inner();
			for(var j=0;j<i2s.length;++j) {
				if( subtypeOf(t1,i2s[j]) ){
					return true;
				}
			}
			return false;
		}
		
		if( t1.type === types.IntersectionType && t2.type !== types.IntersectionType ){
			// one of t1s alts is t2
			var i1s = t1.inner();
			for(var j=0;j<i1s.length;++j) {
				if( subtypeOf(i1s[j],t2) ){
					return true;
				}
			}
			return false;
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
				return subtypeOf( t1.inner(), t2.inner() );
			case types.ReferenceType:
				return subtypeOf( t1.location(), t2.location() );
			case types.RelyType: {
				return subtypeOf( t1.rely(), t2.rely() ) &&
					subtypeOf( t1.guarantee(), t2.guarantee() );
			}
			case types.GuaranteeType: {
				return subtypeOf( t1.guarantee(), t2.guarantee() ) &&
					subtypeOf( t1.rely(), t2.rely() );
			}
			case types.FunctionType:
				return subtypeOf( t2.argument(), t1.argument() )
					&& subtypeOf( t1.body(), t2.body() );
			case types.RecordType:{
				if( !t1.isEmpty() && t2.isEmpty() )
					return false;

				// all fields of t2 must be in t1
				var t1fields = t1.getFields();
				var t2fields = t2.getFields();				
				for( var i in t2fields ){
					if( !t1fields.hasOwnProperty(i) ||
						!subtypeOf( t1fields[i], t2fields[i] ) ){
						return false;
					}
				}
				return true;
			}
			case types.TupleType: {
				var t1s = t1.getValues();
				var t2s = t2.getValues();
				if( t1s.length !== t2s.length )
					return false;
				for( var i=0;i<t1s.length;++i )
					if( !subtypeOf( t1s[i], t2s[i] ) )
						return false;
				return true;
			}
			case types.StackedType:
				return subtypeOf( t1.left(), t2.left() ) &&
					subtypeOf( t1.right(), t2.right() );
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
						if( subtypeOf(curr,tmp) ){
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
						if( subtypeOf(curr,tmp) ){
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
						if( subtypeOf(curr,tmp) ){
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
						!subtypeOf( t1.inner(i1s[i]), j ) )
						return false;
				}
				return true;
			}
			case types.CapabilityType:
				return subtypeOf( t1.location(), t2.location() ) &&
					subtypeOf( t1.value(), t2.value() );
				
			case types.ForallType:		
			case types.ExistsType:{
				
				if( t1.id().type !== t2.id().type )
					return false;
				
				// if needs renaming
				if( t1.id().name() !== t2.id().name() ){
					var tmp = substitutionVarsOnly( t2.inner(), t2.id(), t1.id() );
					return subtypeOf( t1.inner(), tmp );
				}

				return subtypeOf( t1.inner(), t2.inner() );
			}

			case types.TypeVariable:
			case types.LocationVariable: {
					return t1.name() === t2.name();
			}

			case types.DefinitionType:{
				if( t1.definition() === t2.definition() ){
					var t1s = t1.args();
					var t2s = t2.args();
					if( t1s.length !== t2s.length )
						return false;
					for( var i=0;i<t1s.length;++i )
						if( !subtypeOf( t1s[i], t2s[i] ) )
							return false;
					return true;
				}

				// different definitions
				var a = t1.definition();
				var b = t2.definition();	
				
				// already seen
				if( typedef_sub.contains(a,b) ){
					return typedef_sub.get(a,b);
				}
				
				// assume the same, should fail elsewhere if wrong assuming
				typedef_sub.set(a,b,true);
				// unfold and try again
				var tmp = subtypeOf( unAll(t1,false,true), unAll(t2,false,true) );
				typedef_sub.set(a,b,tmp);
					
				return tmp;
			}
			default:
				error( "@subtype: Not expecting " +t1.type );
		}

	};
	
	//
	// TYPING ENVIRONMENT
	//
	
	// The typing environment is a spaghetti stack where the parent
	// may be shared among several different typing environments.
	// All methods return:
	// 	undefined - new element collides with a previously existing one;
	//  null/value - if all OK.
	var Environment = function(parent,defocus_up){
		// note that set only works at the local level (i.e. it will never
		// attempt to set something in an upper-level).

		// CAREFUL: '$' and '#' cannot be source-level identifiers
		var TYPE_INDEX='$';
		//var CAP_INDEX='#';
		
		// meant to be $protected fields
		this.$map = {};
		this.$caps = [];
		this.$parent = parent;
		
		// scope methods		
		this.newScope = function(dg_up){
			return new Environment(this,dg_up);
		}
		this.endScope = function(){
			return this.$parent;
		}
		
		// operations over IDENTIFIERS
		this.set = function(id,value){
			var tmp = this;
			while( tmp !== null ){
				if ( tmp.$map.hasOwnProperty(id) )
					return undefined; // already exists
				tmp = tmp.$parent; // check parent
			}
			
			this.$map[id] = value;
			return true; // ok
		}
		this.get = function(id,cond){ // condition for removal
			if ( this.$map.hasOwnProperty(id) ){
				var tmp = this.$map[id];
				if( cond !== undefined && cond(tmp) ){
					// ensures that it is no longer listed
					delete this.$map[id];
				}
				return tmp;
			}
			if( this.$parent === null )
				return undefined;
			return this.$parent.get(id,cond);
		}
		
		// operations over VARIABLES
		// (includes both TypeVariables and LocationVariables)
		this.setType = function(id,value){
			// type variables cannot be hidden, must be unique
			// otherwise it would either require renaming collisions
			// or could allow access to parts that collide. 
			if( this.getType(id) !== undefined )
				return undefined; // already there
			return this.set(TYPE_INDEX+id,value);
		}
		this.getType = function(id){
			return this.get(TYPE_INDEX+id);
		}
		
		// other...
		this.size = function(){
			return Object.keys(this.$map).length+
					this.$caps.length+
				( this.$parent === null ? 0 : this.$parent.size() );
		}
		
		this.clone = function(){
			var env = this.$parent !== null ?
				new Environment( this.$parent.clone() ) :
				new Environment( null );

			for( var i in this.$map ){
				// assuming it is OK to alias content (i.e. immutable stuff)
				env.set( i, this.$map[i] );
			}
			for( var i=0; i<this.$caps.length;++i ){
				env.setCap( this.$caps[i] );
			}
			
			return env;
		}

		
		// no order is guaranteed!
		this.visit = function(all,f){
			for( var i in this.$map ){
				var isType = (i[0] === TYPE_INDEX);
				f(i,this.$map[i],false,isType);
			}
			for( var i=0; i<this.$caps.length;++i ){
				f(null,this.$caps[i],true,false);
			}
			if( all && this.$parent !== null )
				this.$parent.visit(all,f);
		}
		
		
	};
	
	
	// TypeVariables must be upper cased.
	var isTypeVariableName = function(n){
		return n[0] === n[0].toUpperCase();
	}
	
	//
	// TYPE CHECKER
	//
		
	/**
	 * Attempts to merge the two types given as argument.
	 * @return undefined if they cannot be merged, or the type that is
	 * 	compatible with both.
	 */
	var mergeType = function(t1,t2){
		if( subtypeOf(t1,t2) )
			return t2;
		if( subtypeOf(t2,t1) )
			return t1;

		//t1 = unAll(t1, false, true);
		//t2 = unAll(t2, false, true);
		// if bang mismatch, we need to not consider the sum as banged because
		// our types cannot do a case on whether the type is liner or pure
		var b1 = t1.type === types.BangType;
		var b2 = t2.type === types.BangType;
		
		if( b1 ^ b2 ){
			if( b1 ) t1 = t1.inner();
			if( b2 ) t2 = t2.inner();
		}
		
		var s1 = t1.type === types.StackedType;
		var s2 = t2.type === types.StackedType;
		
		if( s1 ^ s2 ){
			if( !s1 ) t1 = new StackedType(t1,NoneType);
			if( !s2 ) t2 = new StackedType(t2,NoneType);
		}
		
		if( t1.type !== t2.type )
			return undefined;
		// both the same type
		
		if( t1.type === types.StackedType ){
			var left = mergeType( t1.left(), t2.left() );
			if( left === undefined )
				return undefined;
			var right = mergeType( t1.right(), t2.right() );
			if( right === undefined ){
				// if they cannot be merged, then they are alternatives
				// TODO: maybe partially merge is possible?
				right = new AlternativeType();
				right.add( t1.right() );
				right.add( t2.right() );
			}
			return new StackedType(left,right);
		}
		
		if( t1.type === types.BangType ){
			var tmp = mergeType( t1.inner(),t2.inner() );
			if( tmp !== undefined )
				return new BangType( tmp );
		}
		
		if( t1.type === types.SumType ){
			// merge both types
			var tmp = new SumType();
			// add all the labels to the temporary sum
			var tags = t1.tags();
			for( var i in tags ){
				tmp.add( tags[i], t1.inner(tags[i] ) )
			}
			// now check the other to make sure any overlapping is ok or add
			// anything extra that it may have
			tags = t2.tags();
			for( var i in tags ){
				var overlap = tmp.inner(tags[i]);
				if( overlap !== undefined ){
					// make sure they match
					if( !equals( overlap, t2.inner(tags[i]) ))
						return undefined;
				}
				else{
					// make sure it was added.
					if( tmp.add( tags[i], t2.inner(tags[i] ) ) === undefined )
						return undefined;
				}
			}
			return tmp;
		}
		
		// all other cases must have exactly the same type
		if( equals(t1,t2) )
			return t1;
		// should subtyping replace equals? i.e.:
		// if( subtypeOf(t1,t2) ) return t2;
		// if( subtypeOf(t2,t1) ) return t1;
			
		return undefined;
	}

	/*
	 * bang -- remove bang(s)? !A <: A
	 * rec -- unfold recursive definition(s)?
	 */
	var unAll = function(t,bang,rec){
		var MAX = 100;
		
		while( MAX-->0 ){
			
			// by subtyping rule: !A <: A
			if( bang && t.type === types.BangType ){
				t = t.inner();
				continue;
			}
			
			// by unfold definition
			if( rec && t.type === types.DefinitionType ){
				t = unfoldDefinition(t);
				continue;
			}
			
			break;
		}

		if( MAX === 0 ){
			console.debug('@unAll: MAX UNFOLD REACHED, '+t);
			// returns whatever we got, will likely fail due to a packed
			// definition anyway. But it's not our fault that you gave us a type
			// that is bogus/infinite recursive!
		}
		return t;

	}
		
	// attempts to convert type to bang, if A <: !A
	var purify = function(t){
		t = unAll(t,false,true);	
		if( t.type !== types.BangType ){
			var tmp = new BangType(t);
			if( subtypeOf(t,tmp) )
				return tmp;
		}
		return t;		
	}
	
	
	var unfoldDefinition = function(d){
		if( d.type !== types.DefinitionType ||
				typedef.isInRecDefs() )
			return d;
		
		var t = typedef.getDefinition(d.definition());
		var args = d.args();
		var pars = typedef.getType(d.definition());
		// type definitions will only replace Type or Location Variables, we
		// can use the simpler kind of substitution.
		for(var i=0;i<args.length;++i){
			t = substitutionVarsOnly(t,pars[i],args[i]);
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
	p = unAll(p,false,true);
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
		p = unAll(p,false,true);
		
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
		
		assert( subtypeOf( s, p.rely() ) ||
			('Invalid Step: '+s+' VS '+p.rely()), ast );
		
		var next = p.guarantee();
		assert( next.type === types.GuaranteeType ||
			('Expecting GuaranteeType, got: '+next.type), ast);

		var g = next.guarantee();
		assert( subtypeOf( g, m ) || ('Incompatible: '+g+' vs '+m), ast );
	
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
		p = unAll(p,false,true);
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
		p = unAll(p,false,true);

		// unchanged
		if( p.type === types.NoneType ){
			// nothing to be matched
			return { state : s, protocol: p, other: o };
		}

		// now state
		if( s.type === types.AlternativeType ){
			var base = null;
			var alts = s.inner();
//XXX does none mess this up?
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
		assert( subtypeOf( s, p.rely() ) ||
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
		p = unAll(p,false,true);
		
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
		
		assert( subtypeOf( s, p.rely() ) ||
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
			if( subtypeOf(s,tmp[0]) &&
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
			if( subtypeOf(s,tmp[0]) &&
					subtypeOf(p,tmp[1]) && 
					subtypeOf(a,tmp[2]) &&
					subtypeOf(b,tmp[3]) )
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
		if( ast.kind === AST.kinds.SHARE ){
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

			case AST.kinds.SUBTYPE:
			return function( ast, env ){
				var left = check( ast.a, env );
				var right = check( ast.b, env );
				var s = subtypeOf(left,right);
				assert( s==ast.value || ('Unexpected Result, got '+s+' expecting '+ast.value), ast );
				return left;
			};


			case AST.kinds.SUM_TYPE: 
			return function( ast, env ){
				var sum = new SumType();
				for( var i=0; i<ast.sums.length; ++i ){
					var tag = ast.sums[i].tag;
					assert( sum.add( tag, check( ast.sums[i].exp, env ) ) ||
							"Duplicated tag: "+tag, ast.sums[i]);
				}
				return sum;
			};
			
			case AST.kinds.INTERSECTION_TYPE: 
			return function( ast, env ){
				var alt = new IntersectionType();
				for( var i=0; i<ast.types.length; ++i ){
					alt.add( check( ast.types[i], env ) );
				}
				return alt;
			};
			
			case AST.kinds.ALTERNATIVE_TYPE: 
			return function( ast, env ){
				var alt = new AlternativeType();
				for( var i=0; i<ast.types.length; ++i ){
					alt.add( check( ast.types[i], env ) );
				}
				return alt;
			};
			
			case AST.kinds.STAR_TYPE: 
			return function( ast, env ){
				var star = new StarType();
				for( var i=0; i<ast.types.length; ++i ){
					star.add( check( ast.types[i], env ) );
				}
				return star;
			};
			
			case AST.kinds.NAME_TYPE: 
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
					  tmp.type === types.LocationVariable ) )
						return tmp;
				
				// look for type definitions
				var lookup_args = typedef.getType(label);

				// if found something, that is not yet defined
				if( lookup_args !== undefined &&
						lookup_args.length === 0 )
					return new DefinitionType(label, new Array(0));
		
				assert( 'Unknown type '+label, ast);
			};
			
			case AST.kinds.ID:
				// auxiliary function that only removes (i.e. destructive) if linear
				var destructive = function(t) {
					return t.type !== types.BangType;
				};
			return function( ast, env ){
				var id = ast.text;
				var val = env.get( id, destructive );
			
				assert( val !== undefined || ("Identifier '" + id + "' not found"), ast);

				return val;
			};
			
			
			case AST.kinds.DEFINITION_TYPE:
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
			
			case AST.kinds.TYPE_APP: 
			return function( ast, env ){
				var exp = check( ast.exp, env );
				exp = unAll(exp, true, true);
				assert( exp.type === types.ForallType || 
					('Not a Forall '+exp.toString()), ast.exp );
				
				var packed = check(ast.id, env);
				var variable = exp.id();

				if( variable.type === types.LocationVariable ){
						assert( packed.type === types.LocationVariable ||
							( 'Not LocationVariable: '+packed.type ), ast.id );
				}
				
				if( variable.type === types.TypeVariable ){
						assert( packed.type !== types.LocationVariable ||
							( 'Cannot be LocationVariable' ), ast.id );
				}

				return substitutionVarsOnly( exp.inner(), exp.id(), packed );
			};
			
			case AST.kinds.TAGGED: 
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
			
			case AST.kinds.TUPLE_TYPE:
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
			
			
			case AST.kinds.SHARE: 
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
			case AST.kinds.RELY_TYPE: 
			return function( ast, env ){
				var rely = check( ast.left, env );
				var guarantee = check( ast.right, env );
				if( guarantee.type !== types.GuaranteeType ){
					guarantee = new GuaranteeType( guarantee, NoneType );
				}
				return new RelyType( rely, guarantee );
			};
			
			case AST.kinds.GUARANTEE_TYPE: 
			return function( ast, env ){
				var guarantee = check( ast.left, env );
				var rely = check( ast.right, env );
				return new GuaranteeType( guarantee, rely );
			};
			
			case AST.kinds.REF_TYPE: 
			return function( ast, env ){
				var id = ast.text;
				var loc = env.getType( id );
				
				assert( (loc !== undefined && loc.type === types.LocationVariable) ||
					('Unknow Location Variable '+id), ast );
				
				return new ReferenceType( loc );
			};
			
			case AST.kinds.EXISTS_TYPE: 
			return function( ast, env ){
				var id = ast.id;
				var e = env.newScope();
				
				var variable;
				if( isTypeVariableName(id) )
					variable = new TypeVariable(id);
				else
					variable = new LocationVariable(id);
				
				e.setType( id, variable );

				return new ExistsType( variable, check( ast.type, e ) );
			};
			
			case AST.kinds.FORALL:
			case AST.kinds.FORALL_TYPE: 
			return function( ast, env ){
				var id = ast.id;
				var e = env.newScope();
				
				var variable;
				if( isTypeVariableName(id) )
					variable = new TypeVariable(id);
				else
					variable = new LocationVariable(id);

				e.setType( id, variable );

				// note that ast.exp should have size 1, always.
				return new ForallType( variable, check( ast.exp[0], e ) );
			};
			
			case AST.kinds.RECURSIVE_TYPE: 
			return function( ast, env ){
				var id = ast.id;
				var e = env.newScope();
				
				assert( isTypeVariableName(id) ||
					'Type Variables must be upper-cased', ast );
					
				var variable = new TypeVariable(id);
				e.setType( id, variable );
				return new RecursiveType( variable, check( ast.exp, e ) );
			};
						
			case AST.kinds.NONE_TYPE:
			return function( ast, env ){
				return NoneType;
			};
				
			case AST.kinds.BANG_TYPE:
			return function( ast, env ){
				return new BangType( check( ast.type , env ) );
			};
			
			case AST.kinds.FUN_TYPE: 
			return function( ast, env ){
				return new FunctionType( 
					check( ast.arg, env ),
					check( ast.exp, env )
				);
			};
			
			case AST.kinds.CAP_TYPE: 
			return function( ast, env ){
				var id = ast.id;
				var loc = env.getType( id );
				
				assert( (loc !== undefined && loc.type === types.LocationVariable) ||
					('Unknow Location Variable '+id), ast);

				var type = check( ast.type, env );
				type = purify( type );
				return new CapabilityType( loc, type );
			};
			
			case AST.kinds.STACKED_TYPE: 
			return function( ast, env ){
				return new StackedType(
					check( ast.left, env ),
					check( ast.right, env )
				);
			};
			
			case AST.kinds.CAP_STACK: 
			return function( ast, env ){
				var exp = check( ast.exp, env );
				var cap = check( ast.type, env );

				cap = unAll(cap,false,true);
				
				var c = autoStack ( null, cap, env, ast.type );
				// make sure that the capabilities that were extracted from 
				// the typing environment can be used as the written cap.
				assert( subtypeOf( c , cap ) ||
					('Incompatible capability "'+c+'" vs "'+cap+'"'), ast.type );
				return new StackedType( exp, cap );
			};
			
			case AST.kinds.RECORD_TYPE: 
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
			
			case AST.kinds.PRIMITIVE_TYPE:
			return function( ast, env ){
				// any primitive type is acceptable but only ints, booleans
				// and strings have actual values that match a primitive type.
				return new PrimitiveType(ast.text);
			};

			default:
				return function( ast, env ){
					error( "Not expecting " + ast.kind );
				};
		}

	}
	
	var visitor = {};
	// setup visitors
	for( var i in AST.kinds ){
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
		var inRecDef = false;
		var typedefs = {};
		var typedefs_args = {};

		// reset typedef equality table
		//typedef_eq = new Table();
		typedef_sub = new Table();

		// these 3 methods must be used to avoid attempts at resoving recursive
		// definitions before they are all inserted/defined.
		this.beginRecDefs = function(){ inRecDef = true; };
		this.endRecDefs = function(){ inRecDef = false; };
		this.isInRecDefs = function(){ return inRecDef; };
		
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
			typedef_sub = new Table();
		}
	};

	var type_info;
	var unique_counter;
	//var typedef_eq = new Table();
	var typedef_sub;
	var typedef = new TypeDefinition();

	// exporting these to facilitate testing.	
	exports.subtypeOf = subtypeOf;
	exports.equals = equals;
	exports.typedef = typedef;
	exports.checkProtocolConformance = checkProtocolConformance;
	
	exports.check = function(ast,typeinfo,loader){
		// stats gathering
		var start = new Date().getTime();
		type_info = [];
		try{
			error( (ast.kind === AST.kinds.PROGRAM) || 'Unexpected AST node' );
				
			// reset typechecke's state.
			unique_counter = 0;
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
								new TypeVariable(n) : new LocationVariable(n);
						}
					}
					
					assert( typedef.addType(it.id,args) 
						|| ('Duplicated typedef: '+it.id), it );
				}
				
				// must avoid attempting to unfold what is not yet definied.
				typedef.beginRecDefs();

				for(var i=0;i<ast.typedefs.length;++i){
					var type = ast.typedefs[i];						
					var tmp_env = env.newScope();
					var args = typedef.getType(type.id);
					
					// sets the variables, if there are any to setup
					if( args !== null ){
						for(var j=0;j<args.length;++j){
							// should be both for LocationVariables and TypeVariables
							tmp_env.setType( args[j].name(), args[j] );
						}
					}
					
					// map of type names to typechecker types
					assert( typedef.addDefinition(type.id, check(type.type, tmp_env)) 
						|| ('Duplicated typedef: '+type.id), type );
				}
				
				// ok to allow unfoldings
				typedef.endRecDefs();
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
})(AST,assertF); // required globals

