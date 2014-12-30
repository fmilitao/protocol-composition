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

	newType('StarType',
		function StarType() {
			var types = [];
			this.add = function( inner ){
				types.push(inner);
				return true;
			}
			this.inner = function(){ return types; }
		}
	);
	
	newType('AlternativeType',
		function AlternativeType() {
			var alts = [];
			this.add = function( inner ){
				alts.push(inner);
				return true;
			}
			this.inner = function(){ return alts; }
		}
	);
	
	newType('IntersectionType',
		function IntersectionType() {
			var alts = [];
			this.add = function( inner ){
				alts.push(inner);
				return true;
			}
			this.inner = function(){ return alts; }
		}
	);
	
	newType('ForallType',
		function ForallType( id, inner ) {
			this.id = function(){ return id; }
			this.inner = function(){ return inner; }
		}
	);
	
	newType('ExistsType',
		function ExistsType( id, inner ) {
			this.id = function(){ return id; }
			this.inner = function(){ return inner; }
		}
	);
	
	newType('RecordType',
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

	newType('TupleType',
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
	
	newType('LocationVariable',
		function LocationVariable( name ){
			var n = name === null ? 't<sub>'+(unique_counter++)+'</sub>' : name;
			
			this.name = function(){ return n; }
			this.clone = function( n ){ return new LocationVariable(n); }
		}
	);
	
	newType('TypeVariable',
		function TypeVariable( name ){
			var n = name === null ? 'T<sub>'+(unique_counter++)+'</sub>' : name;
			
			this.name = function(){ return n; }
			this.clone = function( n ){ return new TypeVariable(n); }
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
		_add( types.TopType, function(){ return 'top'; });
		
	})();

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
		_add( types.TopType, _visitor[types.PrimitiveType] );

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
	 * The typing environment is a spaghetti stack where the parent
	 * may be shared among several different typing environments.
	 * All methods return:
	 * 	undefined - new element collides with a previously existing one;
	 *  null/value - if all OK.
	 */
	var Environment = function(parent){
		// note that set only works at the local level (i.e. it will never
		// attempt to set something in an upper-level).

		// CAREFUL: '$' cannot be a source-level identifier
		var TYPE_INDEX='$';
		
		// meant to be $protected fields
		this.$map = {};
		this.$caps = [];
		this.$parent = parent;
		
		// scope methods		
		this.newScope = function(){
			return new Environment(this);
		}
		this.endScope = function(){
			return this.$parent;
		}
		
		// operations over IDENTIFIERS
		this.set = function(id,value){
			// check if 'id' exists
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

		// returns the depth of 'id' in the spaghetti stack (current is 1)
		// returns -1 if not found.
		this.getTypeDepth = function(id){
			if ( this.$map.hasOwnProperty(id) ){
				return 1;
			}
			if( this.$parent === null )
				return -1; // not found
			return 1+this.$parent.getTypeDepth(id);
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

	exports.assert = assert;
	exports.error = error;
	exports.Environment = Environment;
	exports.isFree = isFree;
	exports.types = types;
	exports.factory = fct;

	return exports;

})( assertF ); // required globals

