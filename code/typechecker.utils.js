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
			var tags = {}; // FIXME switch do using Map instead
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
			var fields = {}; //FIXME which to map instead
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
	
	var _Variable = function( obj, name, index ){
		var n = name;
		var i = index;
		
		obj.index = function(){ return i; }
		obj.name = function(){ return n; }
		obj.copy = function(j){ return new obj.constructor(name,j); }
	};

	newType('LocationVariable',
		function LocationVariable( name, index ){
			_Variable( this, name, index );
		}
	);
	
	newType('TypeVariable',
		function TypeVariable( name, index ){
			_Variable( this, name, index );
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
		function DefinitionType( definition_name, arg ){
			this.definition = function(){ return definition_name; }
			this.args = function(){ return arg; }
		}
	);
	
	
	// append 'toString' method to types
	// toString( indexesOnly ) // undefined means false
	// if indexesOnly == true then it will only print variable's indexes, not their names.
	(function(){
		// defines which types get wrapping parenthesis
		var _wrap = function(t,v){
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
		var _add = function(t,fun){
			error( !fct[t].hasOwnProperty('toString') || ("Duplicated " +k) );
			fct[t].prototype.toString = fun;
		};
		
		_add( types.FunctionType, function(v){
			return _wrap( this.argument(), v )+" -o "+_wrap( this.body(), v );
		} );
		
		_add( types.BangType, function(v){
			return "!"+_wrap( this.inner(), v );
		} );

		_add( types.RelyType, function(v){
			return _wrap( this.rely(), v )+' => '+_wrap( this.guarantee(), v );
		} );

		_add( types.GuaranteeType, function(v){
			return _wrap( this.guarantee(), v )+' ; '+_wrap( this.rely(), v );
		} );
		
		_add( types.SumType, function(v){
			var tags = this.tags();
			var res = [];
			for( var i in tags ){
				res.push( tags[i]+'#'+_wrap( this.inner(tags[i]), v ) ); 
			}	
			return res.join('+');
		} );

		_add( types.StarType, function(v){
			var inners = this.inner();
			var res = [];
			for( var i=0; i<inners.length; ++i )
				res.push( _wrap( inners[i], v ) ); 
			return res.join(' * ');
		} );
		
		_add( types.AlternativeType, function(v){
			var inners = this.inner();
			var res = [];
			for( var i=0; i<inners.length; ++i )
				res.push( _wrap( inners[i], v ) ); 
			return res.join(' (+) ');
		} );
		
		_add( types.IntersectionType, function(v){
			var inners = this.inner();
			var res = [];
			for( var i=0; i<inners.length; ++i )
				res.push( _wrap( inners[i], v ) ); 
			return res.join(' & ');
		} );
		
		_add( types.ExistsType, function(v){
			return 'exists'+(v?'':' '+this.id().name())
				+( !this.bound()?'':'<:'+_wrap( this.bound(), v ))
				+'.'+_wrap( this.inner(), v );
		} );
		
		_add( types.ForallType, function(v){
			return 'forall'+(v?'':' '+this.id().name())
				+( !this.bound() ? '':'<:'+_wrap( this.bound(), v ))
				+'.'+_wrap( this.inner(), v );
		} );
		
		_add( types.ReferenceType, function(v){
			return "ref "+_wrap( this.location(), v );
		} );
		
		_add( types.CapabilityType, function(v){
			return 'rw '+_wrap( this.location(), v )+' '+_wrap( this.value(), v );
		} );
		
		_add( types.StackedType, function(v){
			return _wrap( this.left(), v )+' :: '+_wrap( this.right(), v );
		} );
		
		_add( types.RecordType, function(v){
			var res = [];
			var fields = this.getFields();
			for( var i in fields )
				res.push(i+": "+_wrap( fields[i], v ) );
			return "["+res.join()+"]";
		} );
		
		_add( types.TupleType, function(v){
			var res = [];
			var fields = this.inner();
			for( var i in fields )
				res.push( _wrap( fields[i], v ) );
			return "["+res.join()+"]";
		} );
		
		_add( types.DefinitionType, function(v){
			if( this.args().length > 0 ){
				var args = this.args();
				var tmp = [];
				for( var i=0; i<args.length;++i ){
					tmp.push( _wrap( args[i], v ) );
				}
				return _wrap( this.definition(), v )+'['+ tmp.join() +']';
			}
			return _wrap( this.definition(), v );
		} );
		
		var tmp = function(v){
			if( !v )
				return this.name()+'^'+this.index(); 
			return this.index();
		};
		_add( types.LocationVariable, tmp );
		_add( types.TypeVariable, tmp );
		_add( types.PrimitiveType, function(v){ return this.name(); } );
		
		_add( types.NoneType, function(v){ return 'none'; });
		_add( types.TopType, function(v){ return 'top'; });
		
	})();
	
	/**
	 * The typing environment is a spaghetti stack where the parent
	 * may be shared among several different typing environments.
	 * All methods return:
	 * 	undefined - new element collides with a previously existing one;
	 *  null/value - if all OK.
	 */
	var Environment = function(up){

		// CAREFUL: the following cannot be a source-level identifiers.
		// These chars are used to distinguish between variables, etc. 
		// that are all sotred in the same map.
		const  TYPE_INDEX = '$';
		const BOUND_INDEX = '#';
		
		var map = new Map();
		var parent = up;
		
		// scope methods		
		this.newScope = function(){
			return new Environment(this);
		}
		this.endScope = function(){
			return parent;
		}
		
		// operations over IDENTIFIERS
		this.set = function(id,value){
			// does not search up. ALLOWS NAME COLISIONS/HIDDING with upper levels.
			// check if 'id' exists at this level
			if( map.has(id) )
				return undefined; // already exists
			map.set( id, value );
			return true; // ok
		}

		this.get = function(id){
			if ( map.has(id) ){
				return map.get(id);
			}
			if( parent === null )
				return undefined;
			return parent.get(id);
		}
		
		// operations over TypeVariables / LocationVariables
		this.setType = function(id,value){
			return this.set(TYPE_INDEX+id,value);
		}
		this.getType = function(id){
			return this.get(TYPE_INDEX+id);
		}
		// operations over bounds
		this.setBound = function(id,bound){
			return this.set(BOUND_INDEX+id,bound);
		}
		this.getBound = function(id){
			return this.get(BOUND_INDEX+id);
		}

		// returns the depth of 'id' in the spaghetti stack, starting at 0.
		// returns -1 if not found.
		this.getTypeDepth = function(id){
			if ( map.has(TYPE_INDEX+id) ){
				return 0;
			}
			if( parent === null )
				return -1; // not found

			var tmp = parent.getTypeDepth(id);
			if( tmp === -1 ) 
				return tmp;
			return 1+tmp;
		}
		
		this.clone = function(){
			var env = parent !== null ?
				new Environment( parent.clone() ) :
				new Environment( null );

			map.forEach(function(k,v){
				// assuming it is OK to alias types/content (i.e. all immutable stuff)
				env.set( k, v );
			});
			
			return env;
		}

		// no order is guaranteed!
		this.forEach = function(f){
			map.forEach(function(i,v){
				var isType = (i[0] === TYPE_INDEX);
				var isBound = (i[0] === BOUND_INDEX );
				var id = ( isType || isBound ) ? i.substring(1) : i;

				f( i, id, v, isBound, isType );
			});
			
			if( parent !== null )
				parent.forEach(f);
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
	exports.Environment = Environment;
	exports.TypeDefinition = TypeDefinition;
	exports.types = types;
	exports.factory = fct;

	return exports;

})( assertF ); // required globals

