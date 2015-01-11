// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

/**
 * INCLUDE 'parser.js' (contains required global variables):
 *  assertf : for error handling/flagging.
 */

var TypeChecker = (function( assertF ){

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

	newType('FunctionType',
		function FunctionType( argument, body ) {
			this.argument = function(){ return argument; }
			this.body = function(){ return body; }
		}
	);
	
	newType('BangType',
		function BangType( inner ) {
			this.inner = function(){ return inner; }
		}
	);
	
	newType('SumType',
		function SumType() {
			var tags = new Map();
			this.add = function( tag, inner ){
				if ( tags.has(tag) )
					return undefined; // already exists!
				tags.set( tag, inner );
				return true;
			}
			// assumes no one will modify this map
			this.tags = function(){
				return tags;
			}
			this.inner = function(tag){
				return tags.get(tag);
			}
		}
	);

	var _Init = function( obj ){
		var v = [];
		obj.add = function( inner ){
			v.push(inner);
			return true;
		}
		obj.inner = function(){ return v; }
	}

	newType('StarType',
		function StarType() {
			_Init( this );
		}
	);
	
	newType('AlternativeType',
		function AlternativeType() {
			_Init( this );
		}
	);
	
	newType('IntersectionType',
		function IntersectionType() {
			_Init( this );
		}
	);

	newType('TupleType',
		function TupleType(){
			_Init( this );
		}
	);
	
	newType('ForallType',
		function ForallType( id, inner, bound ) {
			this.id = function(){ return id; }
			this.inner = function(){ return inner; }
			this.bound = function(){ return bound; }
		}
	);
	
	newType('ExistsType',
		function ExistsType( id, inner, bound ) {
			this.id = function(){ return id; }
			this.inner = function(){ return inner; }
			this.bound = function(){ return bound; }
		}
	);
	
	newType('RecordType',
		function RecordType(){
			var fields = new Map();
			this.add = function(id, type) {
				if ( fields.has(id) ){
					return undefined;
				}
				fields.set( id, type );
				return true;
			}
			this.select = function(id) {
				return fields.get(id);
			}
			this.isEmpty = function(){
				return fields.size===0;
			}
			// note: assumes no one will attempt to change the map
			this.fields = function(){
				return fields;
			}
		}
	);
	
	newType('NoneType',
		function NoneType(){
			// intentionally empty	
		}
	);
	
	newType('TopType',
		function TopType(){
			// intentionally empty	
		}
	);

	newType('ReferenceType',
		function ReferenceType( location ){
			this.location = function(){ return location; }
		}
	);

	newType('StackedType',
		function StackedType( left, right ){
			this.left = function(){ return left; }
			this.right = function(){ return right; }
		}
	);

	newType('CapabilityType',
		function CapabilityType( loc, val ){
			this.location = function(){ return loc; }
			this.value = function(){ return val; }
		}
	);
	
	var _Variable = function( obj, name, index, bound ){
		obj.index = function(){ return index; }
		obj.name = function(){ return name; }
		obj.bound = function(){ return bound; }
		obj.copy = function(j){ return new obj.constructor(name,j,bound); }
	};

	newType('LocationVariable',
		function LocationVariable( name, index ){
			_Variable( this, name, index, null );
		}
	);
	
	newType('TypeVariable',
		function TypeVariable( name, index, bound ){
			_Variable( this, name, index, bound );
		}
	);
	
	newType('PrimitiveType',
		function PrimitiveType( name ){
			this.name = function(){ return name; }
		}
	);
	
	newType('RelyType',
		function RelyType( rely, guarantee ){
			this.rely = function(){ return rely; }
			this.guarantee = function(){ return guarantee; }
		}
	);

	newType('GuaranteeType',
		function GuaranteeType( guarantee, rely ){
			this.rely = function(){ return rely; }
			this.guarantee = function(){ return guarantee; }
		}
	);

	newType('DefinitionType',
		function DefinitionType( definition_name, arg, typedef ){
			this.definition = function(){ return definition_name; }
			this.args = function(){ return arg; }
			// these fetch from the typedef map
			this.getDefinition = function(){
				return typedef.getDefinition(definition_name);
			}
			this.getParams = function(){
				return typedef.getType(definition_name);
			}
			this.getTypeDef = function(){
				return typedef;
			}
		}
	);
	
	
	// append 'toString' method to types
	// toString( indexesOnly ) // undefined means false
	// if indexesOnly == true then it will only print variable's indexes, not their names.
	(function(){

		// defines which types get wrapping parenthesis
		var wrap = function(t,v){
			if( t.type === types.ReferenceType ||
				t.type === types.FunctionType ||
				t.type === types.StackedType ||
				t.type === types.StarType || 
				t.type === types.AlternativeType ||
				t.type === types.SumType ){
					return '('+t.toString(v)+')';
				}
			return t.toString(v);
		};
		
		var setupToString = function(type){
			switch( type ){
				
				case types.FunctionType:
				return function( v ){
					return wrap( this.argument(), v )+" -o "+wrap( this.body(), v );
				};
				
				case types.BangType:
				return function( v ){
					return "!"+wrap( this.inner(), v );
				};

				case types.RelyType:
				return function( v ){
					return wrap( this.rely(), v )+' => '+wrap( this.guarantee(), v );
				};

				case types.GuaranteeType:
				return function( v ){
					return wrap( this.guarantee(), v )+' ; '+wrap( this.rely(), v );
				};
		
				case types.SumType:
				return function( v ){
					var res = [];
					this.tags().forEach( function(value,key){
						res.push( key+'#'+wrap( value, v ) ); 
					});
					return res.join('+');
				};

				case types.StarType:
				return function( v ){
					var inners = this.inner();
					var res = [];
					for( var i=0; i<inners.length; ++i )
						res.push( wrap( inners[i], v ) ); 
					return res.join(' * ');
				};
		
				case types.AlternativeType:
				return function( v ){
					var inners = this.inner();
					var res = [];
					for( var i=0; i<inners.length; ++i )
						res.push( wrap( inners[i], v ) ); 
					return res.join(' (+) ');
				};
				
				case types.IntersectionType:
				return function( v ){
					var inners = this.inner();
					var res = [];
					for( var i=0; i<inners.length; ++i )
						res.push( wrap( inners[i], v ) ); 
					return res.join(' & ');
				};
				
				case types.ExistsType:
				return function( v ){
					return 'exists'+(v?'':' '+this.id().name())
						+( !this.bound()?'':'<:'+wrap( this.bound(), v ))
						+'.'+wrap( this.inner(), v );
				};
				
				case types.ForallType:
				return function( v ){
					return 'forall'+(v?'':' '+this.id().name())
						+( !this.bound() ? '':'<:'+wrap( this.bound(), v ))
						+'.'+wrap( this.inner(), v );
				};
		
				case types.ReferenceType:
				return function( v ){
					return "ref "+wrap( this.location(), v );
				};
		
				case types.CapabilityType:
				return function( v ){
					return 'rw '+wrap( this.location(), v )+' '+wrap( this.value(), v );
				};
				
				case types.StackedType:
				return function( v ){
					return wrap( this.left(), v )+' :: '+wrap( this.right(), v );
				};
		
				case types.RecordType:
				return function( v ){
					var res = [];
					this.fields().forEach(function(value,key){
						res.push( key +": "+wrap( value, v ) );
					});
					return "["+res.join()+"]";
				};
				
				case types.TupleType:
				return function( v ){
					var res = [];
					var fields = this.inner();
					for( var i in fields )
						res.push( wrap( fields[i], v ) );
					return "["+res.join()+"]";
				};
				
				case types.DefinitionType:
				return function(v){
					if( this.args().length > 0 ){
						var args = this.args();
						var tmp = [];
						for( var i=0; i<args.length;++i ){
							tmp.push( wrap( args[i], v ) );
						}
						return wrap( this.definition(), v )+'['+ tmp.join() +']';
					}
					return wrap( this.definition(), v );
				};

				case types.LocationVariable:
				case types.TypeVariable:
				return function( v ){
					if( !v )
						return this.name()+'^'+this.index();
					
					var str = '';
					// only add type bound if it is a TypeVariable
					if( this.type === types.TypeVariable ){
						var b = this.bound();
						// with a valid bound
						if( b !== null ) {
							// for clarity we use '$' instead of '<:'
							str = '$'+b.toString(v);
						}
					}

					return this.index()+str;
				};

				case types.PrimitiveType:
				return function(v){ return this.name(); };
		
				case types.NoneType:
				return function(v){ return 'none'; };
				
				case types.TopType:
				return function(v){ return 'top'; };

				default:
				error( '@setupToString: Not expecting type: '+type );
			}
		}

		// add toString to all types
		for( var i in types ){
			var t = types[i];
			var fun = setupToString( t );
			error( !fct[t].hasOwnProperty('toString') || ("Duplicated " +t) );
			fct[t].prototype.toString = fun;
		}
		
	})();
	
	/**
	 * The typing environment is a spaghetti stack where the parent
	 * may be shared among several different typing environments.
	 * All methods return:
	 * 	undefined - new element collides with a previously existing one;
	 *  null/value - if all OK.
	 */
	var Gamma = function( typedef, parent, id, type, bound ){
		// id, type, bound are left undefined when called with:
		// new Gamma( typedef, null );

		this.getTypeDef = function(){
			return typedef;
		}
		
		// scope methods		
		this.newScope = function( id, type, bound ){
			return new Gamma( typedef, this, id, type, bound );
		}
		this.endScope = function(){
			return parent;
		}

		// getters
		this.getType = function( index ) {
			if( index === 0 )
				return type;
			if( parent === null || index < 0 )
				return undefined;
			return parent.getType( index-1 );
		}
		this.getBound = function( index ){
			if( index === 0 )
				return bound;
			if( parent === null || index < 0 )
				return undefined;
			return parent.getBound( index-1 );
		}
		this.getTypeByName = function( name ) {
			if( name === id )
				return type;
			if( parent === null )
				return undefined;
			return parent.getTypeByName( name );
		}

		// returns the depth of 'name' in the spaghetti stack.
		// return: starts at 0, -1 if not found.
		this.getNameIndex = function( name ){
			if ( id === name ){
				return 0;
			}
			if( parent === null )
				return -1; // not found

			var tmp = parent.getNameIndex( name );
			if( tmp === -1 ) 
				return tmp;
			return 1+tmp;
		}

		this.forEach = function( f, i ){
			if( i === undefined )
				i = 0;

			f( i, id, type, bound );
			
			if( parent !== null )
				parent.forEach( f, i+1 );
		}
		
	};

	var TypeDefinition = function(){
		var typedefs;
		var typedefs_args;
		
		this.addType = function(name,array){
			if( typedefs_args.has(name) )
				return false;
			typedefs_args.set( name, array );
			return true;
		};
		this.addDefinition = function(name,definition){
			if( typedefs.has(name) )
				return false;
			typedefs.set( name, definition );
			return true;
		};
		this.getType = function(name){
			return typedefs_args.get(name);
		};
		this.getDefinition = function(name){
			return typedefs.get(name);
		};
		this.reset = function(){
			typedefs = new Map();
			typedefs_args = new Map();
		};

		this.reset();
	};

	exports.assert = assert;
	exports.error = error;
	exports.Gamma = Gamma;
	exports.TypeDefinition = TypeDefinition;
	exports.types = types;
	exports.factory = fct;

	return exports;

})( assertF ); // required globals

