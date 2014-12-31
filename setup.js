// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

var DEBUG_MSG = true;
var worker_enabled = true;
var default_file = 'examples/welcome.txt';
var default_style = 'ace/theme/mono_industrial'; //NOTE: cannot be wrapped in quotes.

//load examples given as parameters
var parameters = document.URL.split('?');
if( parameters.length > 1 ){
	parameters = parameters[1].split('&');
	for( var i=0;i<parameters.length;++i ){
    	var tmp = parameters[i].split('=');
    	if( tmp.length > 1 ){
    		var option = tmp[0];
    		var value = tmp[1];
    		switch( option ){
    			case 'file': // loads file
    				default_file = value;
    				break;
    			case 'style':
    				default_style = value;
    				break;
    			case 'worker':
					// compares given string with 'true' string.
    				worker_enabled = (value.toLowerCase() === 'true');
    				break;
    			default: // no other options, just ignores
    				break;
    		}
    	}
	}
}

if( !worker_enabled ){
	// import all scripts for debugging
	var importScript = function(file){
		document.write('<script src="'+file+'"><\/script>');
	};

	// uses this GLOBAL var to communicate with fake worker
	var MAIN_HANDLER = null;

	console.log('importing scripts to run locally...');
	importScript('lib/jison.js');
	importScript('code/parser.js');
	importScript('code/typechecker.utils.js');
	importScript('code/typechecker.js');
	importScript('code/worker.js');
	console.log('done.');
}

// HTML element IDs that need to be present in the .html file
const INFO ="info";
const EDITOR = "editor";
const OUTPUT = "output";
const STATUS_BAR = "statusbar";
const EXAMPLES = "examples";
const AUTORUN = "autorun";
const TYPING = 'typing';
const TYPEINFO = 'typeinfo';
// convenient constants to use with jQuery
const _OUTPUT_ = "#"+OUTPUT;
const _AUTORUN_ = "#"+AUTORUN;
const _EXAMPLES_ = "#"+EXAMPLES;
const _CURSOR_ = "#cursor-position";
const _TYPEINFO_ = '#'+TYPEINFO;
const _TYPING_ = '#'+TYPING;
const _RESET_ = '#reset';

var TYPE_INFO_WIDTHS = null;

$(document).ready(function() {

	$.ajaxSetup({ cache: !DEBUG_MSG });

	if( !window.chrome ){
		// warn that it is not chrome
		document.getElementById("chrome_warn").className = "chrome_show";
	}

	//
	// window layout setup
	//

	window.onresize = function () {
		// note that all these constants must be set through javascript
		// or they will not be accessible to use in these computaitons.
		// the values are just empirically picked to look OK.

		var w = window.innerWidth;
		var h = window.innerHeight;

		// all values in pixels
		var controls_height = 20;
		var console_height = 80;
		var split = 270;
		var bar = 35;

		var info = document.getElementById(INFO);
		info.style.width = w+"px";
		info.style.height = bar+"px";

		var editor = document.getElementById(EDITOR);
		//editor.style.left = split+"px";
		editor.style.width = (w)+"px";
		editor.style.height = (h-console_height-controls_height-bar)+"px";
		editor.style.top = bar+"px";

		var controls = document.getElementById(STATUS_BAR);
		//controls.style.left = split+"px";
		controls.style.width = w+"px";
		controls.style.height = (controls_height)+"px";
		controls.style.top = (h-controls_height)+"px";

		var output = document.getElementById(OUTPUT);
		//output.style.left = split+"px";
		output.style.width = w+"px";
		output.style.height = (console_height)+"px";
		output.style.top = (h-console_height-controls_height)+"px";

		var typing = document.getElementById(TYPING);
		typing.style.top = 0+"px";
		typing.style.left = 0+"px";
		typing.style.maxHeight = h+"px";
		typing.style.maxWidth = split+"px";
		TYPE_INFO_WIDTHS = { max : split , limit : w };

	}

 	window.onresize(); // only do this after the rest is initialized!

    //
    // Editor and Buttons setup
    //

    (function(){
    	var entered = false;
    	var panel = $("#config");

    	panel.mouseenter(function(){
			entered = true;
    	});

    	panel.mouseleave(function(){
    		if(entered){
    			panel.fadeToggle(50);
    			entered = false;
    		}
    		//panel.fadeOut('fast');
    	});

	    $("#gear").click(function(){
		
			var position = $(this).offset();
	    	var y = position.top;
	      	var x = position.left;

	    	panel.css({
	    		'left': window.innerWidth-(panel.width())-15, //2, //x-(panel.width()/2),
	    		'top': y-7+(1.5*$(this).outerHeight())
	    		//, 'display': 'block'
	    	});

	    	panel.fadeToggle(50);

	    });
	}());

    var editor = ace.edit(EDITOR);
	var Range = ace.require("ace/range").Range;

	(function(){
    	editor.setTheme(default_style);
    	// selected="selected"
		var STYLE_LIST = $("#editor-style");
		$.get( "ace/ace-themes-list" , function(data) {
			var themes = data.split('\n');
			for( var i=0 ; i<themes.length ; ++i ){
				var name = themes[i];
				name = name.replace('-','/');
				name = name.replace('.js','');
				var option = $('<option/>', {
	        		value: name,
	        		text: name
				});
				STYLE_LIST.append(option);
	    	}
		});

		STYLE_LIST.change(function () {
			var style = $(this).val();
			if( style != '' )
	   			editor.setTheme("ace/"+style);
    	});
	})();

    // disable code folding
    editor.getSession().setFoldStyle("manual");
    editor.getSession().setMode("ace/mode/grammar");
    editor.setShowPrintMargin(false);
    editor.getSession().setTabSize(3);


	(function(){ // Examples buttons.
		var setEditor = function(text){
			// disable event handlers while updating content
			// to avoid having to handle incomplete events
			editor.selection.removeListener('changeCursor', onCursorChange);
			editor.removeListener('change', onChange);

			// set new source code and gain focus.
			editor.getSession().setValue(text);
			editor.focus();

			// re-enable event handlers
			editor.selection.on("changeCursor", onCursorChange);
			editor.on("change", onChange );
			onChange();
		}

		var addExample = function(file,name){
			name = name.replace('.txt','');
			var button = $('<span/>', {
				class: 'b1',
	        	text: name,
	        	title: 'load example',
	        	click: function(){
	        		//button.text(name+' (Loading...)');
	        		button.addClass('b1_load');

	        		$.get( file , function(data) {
						setEditor(data);
						//button.text(name);
						button.removeClass('b1_load');
					});
				}
	    	});
			$(_EXAMPLES_).append(button);
		}

		$.get( "examples/examples-list" , function(data) {
			var examples = data.split('\n');
			for( var i=0 ; i<examples.length ; ++i ){
				if( examples[i][0] != '#' ) // ignore commented stuff
					addExample( 'examples/'+examples[i] , examples[i] );
			}
		});

		// setup editor with default file.
		$.get( default_file , function(data) { setEditor(data); });

		// tests
	    var TEST_LIST = $("#test-file");
		$.get( "examples/tests-list" , function(data) {
			var file = data.split('\n');
			for( var i=0 ; i<file.length ; ++i ){
				if( file[i][0] != '#' ){ // ignore commented out file
					var option = $('<option/>', {
		        		value: 'examples/tests/'+file[i],
		        		text: file[i]
					});
					TEST_LIST.append(option);
				}
	    	}
		});

		TEST_LIST.change(function () {
			var file = $(this).val();
			if( file != '' ){
				$.get( file , function(data) {
					setEditor(data);
				});
			}
    	});
    })();

    var actionButton = function(label,id,title,text){
    	var ctr = $('#controls');
    	ctr.prepend("<div class='action'>"+label+"<button class='exbuttong' id="+id+
    		" title="+title+"><b>"+text+"</b></button></div>");
    };

	(function(){ // Auto-Run button
		actionButton("Autorun: ","autorun",
			"Autorun may crash tab/browser if your code does not terminate.",
			"ON");

		var autorun = true;
		var button = $(_AUTORUN_);
		button.click( function(event){
			autorun = !autorun;
			button.html( autorun ? "<b>ON</b>" : "OFF");
			comm.autorun(autorun);
			editor.focus();
		} );
	})();

	var typeinfo = true;
	(function(){ // Typing-information panel.
		actionButton("Typing Information: ","typeinfo",
			"Type information is shown when the cursor is placed at the beginning of a construct.",
			"SHOW");

		var button = $(_TYPEINFO_);
		var panel = $(_TYPING_);

		// toggle button.
		button.click( function(event){
			typeinfo = !typeinfo;
			if( typeinfo ){
				button.html("<b>SHOW</b>");
				if( panel.html() != '' )
					panel.show();
			}
			else{
				button.html("HIDE");
				panel.fadeOut('fast');
			}
			editor.focus();
		} );

		// quick way to hide just the panel.
		panel.click( function(){
			panel.fadeOut('fast');
			editor.focus();
		} );

		var t;
		panel.hover(function() {
	        window.clearTimeout(t);
	        t = window.setTimeout(function () {
	            panel.animate({"max-width": TYPE_INFO_WIDTHS.limit }, 'fast');
	            //panel.css('max-width',TYPE_INFO_WIDTHS.limit);
	            //panel.removeClass('typing_style');
	            //panel.addClass('typing_show');
	          }, 500);
	    });
	    panel.mouseleave(function() {
	        window.clearTimeout(t);
	        t = window.setTimeout(function () {
	            //panel.css('max-width',TYPE_INFO_WIDTHS.max);
	            panel.animate({"max-width": TYPE_INFO_WIDTHS.max }, 'slow');
	            //panel.removeClass('typing_show');
	            //panel.addClass('typing_style');
	          }, 250);
	    });

	})();

	(function(){
		// reset worker button.
		if( worker_enabled ) {
			actionButton("Re-Start Worker: ","reset",
				"If code does not terminate, you may need to manually reset the worker thread.",
				"RESET");

			var button = $(_RESET_);

			button.click( function(event){
				comm.reset();
				editor.focus();
			});
		}
	})();

	//
	// Boxing Types
	//

	// when hovered over 'triggers' change 'changers' to a boxed style, on out
	// removes that style (which is the initial state).
	var triggers = 'Q';
	var changers = 'q';
	var refreshTypeListners = function(){
		$('.'+changers)
				.css('background-color', 'inherit')
			    .css('outline', 'none')
			    ;

		$('.'+triggers).hover(
		  function(){
			  $(this)
			    .siblings('.'+changers)
			    .css('background-color', 'white')
			    .css('outline', '2px solid #bbbbbb')
			    ;
		  },
		  function(){
			  $(this)
			    .siblings('.'+changers)
			    .css('background-color', 'inherit')
			    .css('outline', 'none')
			    ;
		  }
		);
	};

    //
    // Editor & Listeners Setup
    //

    var out = new function(){
    	var o = $(_OUTPUT_);
    	var t = $(_TYPING_);

    	this.clearAll = function(){
    		o.html('');
    		this.clearTyping();
    	};

    	this.printError = function(error){
    		// uses inner span to print with different colors
    		this.println( "<span class=bad>"+error+"</span>" );
    	}

    	this.println = function(val){
    		var old = o.html();
    		o.html( ( old ? old+'\n' :'' ) + val.toString() );
    	};

    	this.clearTyping = function(){
    		this.printTyping('');
    	}

    	this.printTyping = function( val ){
    		if( val == '' ){
    			t.hide();
    		}else{
    			if( typeinfo )
    				t.show();
    		}
    		t.html( val.toString() );

    		// for boxing types
    		refreshTypeListners();
    	};

    };

    //
    // Handler of (Received) Events
    //

	var handle = {

		//
		// console
		//

		log : function(msg){ console.log( msg ); },
		debug : function(msg){ console.debug( msg ); },
		error : function(msg){ console.error( msg ); },

		//
		// info
		//

		printError : function(msg){
			out.printError(msg);
		},
		clearAll : function(){
			out.clearAll();
		},
		println : function(msg){
			out.println(msg);
		},
		clearTyping : function(){
			out.clearTyping();
		},
		printTyping : function(msg){
			out.printTyping(msg);
		},

		//
		// error handling & annotaitons
		//

		// WARNING: assumes JSONed object
		errorHandler : function(e){
			e = JSON.parse(e); //deserialize object
			var msg = "";

        	var line = 1;
        	var col = 0;
        	var last_line = 1;
        	var last_col = -1;

        	var groupName = null;

			if ( e.hasOwnProperty('ast') && e.ast !== undefined ) {
				line = e.ast.line;
				col = e.ast.col;
				last_line = e.ast.last_line;
				last_col = e.ast.last_col;

				// for printing we must +1 to properly match ACE's counting
				msg += e.kind+" on line "+(e.ast.line+1)+
					(e.ast.col?(":"+e.ast.col):'')+" - ";
			}else{
				groupName = 'Exception:';
			}
			msg += ( e.message || e )+".";

			if( DEBUG_MSG || groupName != null ){
				if( groupName == null ) {
					console.groupCollapsed( '[Debug-Info] '+msg );
				} else {
					// real error, show expanded
					console.group( groupName );
				}
				console.debug("Extra Info: "+e.debug+"\nStack Trace:\n"+e.stack);
				console.groupEnd();
			}
            out.printError( msg );

			handle.updateAnnotations( { reason : msg,
					line : line, col : col,
					last_line : last_line, last_col : last_col } );
		},

    	updateAnnotations : function(res){
    		var session = editor.getSession();

	    	if (res !== null) {
	            session.setAnnotations([{
	                row : res.line,
	                column : res.col,
	                text : res.reason,
	                type : "error",
	                lint : "error"
	            }]);

				// marker stores the last hightlight mark or null if none exists
	            if( marker !== null ){
	            	session.removeMarker( marker );
	            }
	            var tmp = new Range(res.line, res.col,
					( res.last_line ? res.last_line : res.line ),
					// highlight the whole line if no end given
	            	( res.last_col ? res.last_col : session.getLine(res.line).length ));
	            marker = session.addMarker(tmp, "underline_error", "text");
	            //ace_selection
	        } else {
	            // no error, clear old annotations
	            session.clearAnnotations();
	            session.removeMarker( marker );
	            marker = null;
	        }
        }
	};

	var marker = null;

	//
	// Communication Object
	//

	var comm = new function(){

		if( worker_enabled ){

			var worker;

			// launch worker
			this.resetWorker = function() {
				if( worker !== undefined ){
					// stops old worker
					worker.terminate();
				}

				worker = new Worker('code/worker.js');
				worker.addEventListener('message', function(e) {
					var m = e.data;
					try{
						handle[m.kind](m.data);
					}catch(er){
						console.error(er);
					}
				}, false);

				// generic send, tags k as 'kind' and msg as 'data'
				this.send = function(k,msg){
					worker.postMessage({ kind: k, data: msg });
				};
			};

			this.resetWorker();

		}else{

			// make handle function available to worker THIS IS A GLOBAL VAR
			MAIN_HANDLER = handle;

			this.send = function(kind,data) {
				try{
					// imported code should defin global variable 'WORKER_HANDLER' to
					// enable "communication".
					WORKER_HANDLER[kind](data);
				}catch(e){
					console.error(e);
				}
			};

		}

		this.eval = function(){
			this.send('EVAL', editor.getSession().getValue());
		};

		this.checker = function(p){
			this.send('CHECKER', p);
		};

		this.autorun = function(v){
			this.send('AUTO', v);
		};

		this.reset = function(){
			this.resetWorker();
			this.eval();
		};

	};
	// END communication object.

	var cursor_elem = $(_CURSOR_);

    var onCursorChange = function(){
        try{
            var pos = editor.getCursorPosition();
            cursor_elem.html((pos.row+1)+":"+pos.column);
            comm.checker(pos);
        }catch(e){
            // do nothing.
        }
    };

    var onChange = function(e) {
    	// simply re-do everything, ignore diff.
    	// more efficient incremental parser left as future work...
    	comm.eval();
    };

	editor.selection.on("changeCursor", onCursorChange);
    editor.on("change", onChange );

    // the initial run to parse the example text.
    onChange();
    // editor apparently automatically gets focused, even without this.
    editor.focus();


    var setStatus = function(txt){
    	$('#status').text(txt);
    };

    setStatus('Ready.');
});
