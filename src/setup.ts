// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

/// <reference path='../lib/def/ace.d.ts' />
/// <reference path='../lib/def/jquery.d.ts' />
/// <reference path='../lib/def/chrome.d.ts' />

module Setup {

    // HTML element IDs that need to be present in the .html file
    const INFO = "info";
    const EDITOR = "editor";
    const OUTPUT = "output";
    const STATUS_BAR = "statusbar";
    const EXAMPLES = "examples";
    const TYPING = 'typing';
    const TYPEINFO = 'typeinfo';
    // convenient constants to use with jQuery
    const _OUTPUT_ = "#" + OUTPUT;
    const _EXAMPLES_ = "#" + EXAMPLES;
    const _CURSOR_ = "#cursor-position";
    const _TYPEINFO_ = '#' + TYPEINFO;
    const _TYPING_ = '#' + TYPING;
    const _RESET_ = '#reset';

    const IMPORTS = [
        'lib/jison.js',
        'bin/setup.comm.js',
        'bin/ast.js',
        'bin/parser.js',
        'bin/typechecker.types.js',
        'bin/typechecker.utils.js',
        'bin/typechecker.js'];
    const WORKER_JS = 'bin/setup.worker.js';

    let DEBUG_MSG = true;
    let worker_enabled = true;
    let default_file = 'examples/welcome.txt';
    let default_style = 'ace/theme/mono_industrial'; //NOTE: cannot be wrapped in quotes.

    let TYPE_INFO_WIDTHS = null;

    //loads options given as URL parameters
    let parameters = document.URL.split('?');
    if (parameters.length > 1) {
        parameters = parameters[1].split('&');
        for (let parameter of parameters) {
            let tmp = parameter.split('=');
            if (tmp.length > 1) {
                const option = tmp[0];
                const value = tmp[1];
                switch (option) {
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
                    default: // no other valid options, warn ignored params.
                        console.warn('Ignoring unknown option: ' + parameter);
                        break;
                }
            }
        }
    }

    //
    // Loads scripts locally, if to be runned without web worker.
    //

    if (!worker_enabled) {
        console.log('importing scripts to run locally...');
        importScript.apply(null,IMPORTS);
        importScript(WORKER_JS);
        console.log('done.');
    }

    // lays all UI components, also useful when resizing window
    function onResize(ev: UIEvent): any {
        // note that all these constants must be set through javascript
        // or they will not be accessible to use in these computations.
        // the values are just empirically picked to look OK in chrome.

        let w = window.innerWidth;
        let h = window.innerHeight;

        // all values in pixels
        let controls_height = 20;
        let console_height = 80;
        let split = 270;
        let bar = 35;

        let info = document.getElementById(INFO);
        info.style.width = w + "px";
        info.style.height = bar + "px";

        let editor = document.getElementById(EDITOR);
        //editor.style.left = split+"px";
        editor.style.width = (w) + "px";
        editor.style.height = (h - console_height - controls_height - bar) + "px";
        editor.style.top = bar + "px";

        let controls = document.getElementById(STATUS_BAR);
        //controls.style.left = split+"px";
        controls.style.width = w + "px";
        controls.style.height = (controls_height) + "px";
        controls.style.top = (h - controls_height) + "px";

        let output = document.getElementById(OUTPUT);
        //output.style.left = split+"px";
        output.style.width = w + "px";
        output.style.height = (console_height) + "px";
        output.style.top = (h - console_height - controls_height) + "px";

        let typing = document.getElementById(TYPING);
        typing.style.top = bar + "px";
        typing.style.left = (w / 2) + "px";
        typing.style.maxHeight = h + "px";
        typing.style.maxWidth = (w / 2) + "px";
        typing.style.opacity = '0.8';

        TYPE_INFO_WIDTHS = {
            maxWidth: w, defaultWidth: w / 2,
            minLeft: 0, defaultLeft: (w / 2),
            maxOpacity: 1, defaultOpacity: 0.8
        };
    };


    export function onReady() {

        $.ajaxSetup({ cache: !DEBUG_MSG });

        if (!window.chrome) {
            // warn that it is not chrome
            document.getElementById("chrome_warn").className = "chrome_show";
        }

        //
        // window layout setup
        //

        window.onresize = onResize;
        // force initial layout computation
        onResize(null); // only do this after the rest is initialized!

        //
        // Editor and Buttons setup
        //

        // configuration gear

        const panel = $("#config");
        let entered = false;

        panel.mouseenter(function() {
            entered = true;
        });

        panel.mouseleave(function() {
            if (entered) {
                panel.fadeToggle(50);
                entered = false;
            }
            //panel.fadeOut('fast');
        });

        $("#gear").click(function() {

            const position = $(this).offset();
            const y = position.top;
            const x = position.left;

            panel.css({
                'left': window.innerWidth - (panel.width()) - 15, //2, //x-(panel.width()/2),
                'top': y - 7 + (1.5 * $(this).outerHeight())
                //, 'display': 'block'
            });

            panel.fadeToggle(50);

        });


        //

        let editor: any = ace.edit(EDITOR);
        editor.$blockScrolling = Infinity; // FIXME on warning. useful?
        let Range = ace.require("ace/range").Range;

        //
        // theme selector
        //

        editor.setTheme(default_style);
        // selected="selected"
        var STYLE_LIST = $("#editor-style");
        $.get("lib/ace/ace-themes-list", function(data) {
            var themes = data.split('\n');
            for (var i = 0; i < themes.length; ++i) {
                var name = themes[i];
                name = name.replace('-', '/');
                name = name.replace('.js', '');
                var option = $('<option/>', {
                    value: name,
                    text: name
                });
                STYLE_LIST.append(option);
            }
        });

        STYLE_LIST.change(function() {
            var style = $(this).val();
            if (style != '')
                editor.setTheme("ace/" + style);
        });

        // disables code folding
        editor.getSession().setFoldStyle("manual");
        editor.getSession().setMode("ace/mode/grammar");
        editor.setShowPrintMargin(false);
        editor.getSession().setTabSize(3);


        (function() { // Examples buttons.
            var setEditor = function(text) {
                // disable event handlers while updating content
                // to avoid having to handle incomplete events
                editor.selection.removeListener('changeCursor', onCursorChange);
                editor.removeListener('change', onChange);

                // set new source code and gain focus.
                editor.getSession().setValue(text);
                editor.focus();

                // re-enable event handlers
                editor.selection.on("changeCursor", onCursorChange);
                editor.on("change", onChange);
                onChange(null); // FIXME: warning!
            }

            var addExample = function(file, name) {
                name = name.replace('.txt', '');
                var button = $('<span/>', {
                    class: 'b1',
                    text: name,
                    title: 'load example',
                    click: function() {
                        //button.text(name+' (Loading...)');
                        button.addClass('b1_load');

                        $.get(file, function(data) {
                            setEditor(data);
                            //button.text(name);
                            button.removeClass('b1_load');
                        });
                    }
                });
                $(_EXAMPLES_).append(button);
            }

            $.get("examples/examples-list", function(data) {
                var examples = data.split('\n');
                for (var i = 0; i < examples.length; ++i) {
                    if (examples[i][0] != '#') // ignore commented stuff
                        addExample('examples/' + examples[i], examples[i]);
                }
            });

            // setup editor with default file.
            $.get(default_file, function(data) { setEditor(data); });


        })();

        var actionButton = function(label, id, title, text) {
            var ctr = $('#controls');
            ctr.prepend("<div class='action'>" + label + "<button class='exbuttong' id=" + id +
                " title=" + title + "><b>" + text + "</b></button></div>");
        };

        var typeinfo = true;
        (function() { // Typing-information panel.
            actionButton("Typing Information: ", "typeinfo",
                "Type information is shown when the cursor is placed at the beginning of a construct.",
                "SHOW");

            var button = $(_TYPEINFO_);
            var panel = $(_TYPING_);

            // toggle button.
            button.click(function(event) {
                typeinfo = !typeinfo;
                if (typeinfo) {
                    button.html("<b>SHOW</b>");
                    if (panel.html() != '')
                        panel.show();
                }
                else {
                    button.html("HIDE");
                    panel.fadeOut('fast');
                }
                editor.focus();
            });

            // quick way to hide just the panel.
            panel.click(function() {
                panel.fadeOut('fast');
                editor.focus();
            });

            var t;
            panel.hover(function() {
                window.clearTimeout(t);
                t = window.setTimeout(function() {
                    //panel.animate({"max-width": TYPE_INFO_WIDTHS.limit }, 'fast');
                    //panel.css('max-width',TYPE_INFO_WIDTHS.limit);
                    //panel.removeClass('typing_style');
                    //panel.addClass('typing_show');
                    panel.animate({
                        "left": TYPE_INFO_WIDTHS.minLeft,
                        "max-width": TYPE_INFO_WIDTHS.maxWidth,
                        "width": TYPE_INFO_WIDTHS.maxWidth,
                        "opacity": TYPE_INFO_WIDTHS.maxOpacity
                    }, 'fast');
                }, 500);
            });
            panel.mouseleave(function() {
                window.clearTimeout(t);
                t = window.setTimeout(function() {
                    //panel.css('max-width',TYPE_INFO_WIDTHS.max);
                    panel.animate({
                        "left": TYPE_INFO_WIDTHS.defaultLeft,
                        "max-width": TYPE_INFO_WIDTHS.defaultWidth,
                        "width": "auto",
                        "opacity": TYPE_INFO_WIDTHS.defaultOpacity
                    }, 'slow');
                    //panel.animate({"max-width": TYPE_INFO_WIDTHS.max }, 'slow');
                    //panel.removeClass('typing_show');
                    //panel.addClass('typing_style');
                }, 250);
            });

        })();


        //
        // Boxing Types
        //

        // when hovered over 'triggers' change 'changers' to a boxed style, on out
        // removes that style (which is the initial state).
        const triggers = 'Q';
        const changers = 'q';

        function refreshTypeListners() {
            $('.' + changers)
                .css('background-color', 'inherit')
                .css('outline', 'none')
            ;

            $('.' + triggers).hover(
                function() {
                    $(this)
                        .siblings('.' + changers)
                        .css('background-color', 'white')
                        .css('outline', '2px solid #bbbbbb')
                    ;
                },
                function() {
                    $(this)
                        .siblings('.' + changers)
                        .css('background-color', 'inherit')
                        .css('outline', 'none')
                    ;
                }
                );
        };

        //
        // Handler of (Received) Events
        //

        const handler = (function() {

            // output panel & typing panel
            const o = $(_OUTPUT_);
            const t = $(_TYPING_);

            // aux functions
            function clearAll() {
                o.html('');
                clearTyping();
            };

            function printError(error) {
                // uses inner span to print with different colors
                println("<span class=bad>" + error + "</span>");
            };

            function println(val) {
                let old = o.html();
                o.html((old ? old + '\n' : '') + val.toString());
            };

            function clearTyping() {
                printTyping('');
            };

            function printTyping(val) {
                if (val == '') {
                    t.hide();
                } else {
                    if (typeinfo)
                        t.show();
                }
                t.html(val.toString());

                // for boxing types
                refreshTypeListners();
            };

            let marker = null;

            return {

                log: function(msg:string){ console.log(msg); },
                debug: function(msg:string){ console.debug(msg);},
                error: function(msg:string){ console.error(msg); },

                //
                // info
                //

                printError: printError,
                clearAll: clearAll,
                println: println,
                clearTyping: clearTyping,
                printTyping: printTyping,

                //
                // error handling & annotaitons
                //

                // WARNING: assumes JSONed object
                errorHandler: function(e) {
                    e = JSON.parse(e); //deserialize object
                    let msg = "";

                    let line = 1;
                    let col = 0;
                    let last_line = 1;
                    let last_col = -1;

                    let groupName = null;

                    if (e.hasOwnProperty('ast') && e.ast !== undefined) {
                        line = e.ast.line;
                        col = e.ast.col;
                        last_line = e.ast.last_line;
                        last_col = e.ast.last_col;

                        // for printing we must +1 to properly match ACE's counting
                        msg += e.kind + " on line " + (e.ast.line + 1) +
                        (e.ast.col ? (":" + e.ast.col) : '') + " - ";
                    } else {
                        groupName = 'Exception:';
                    }
                    msg += (e.message || e) + ".";

                    if (DEBUG_MSG || groupName != null) {
                        if (groupName == null) {
                            console.groupCollapsed('[Debug-Info] ' + msg);
                        } else {
                            // real error, show expanded
                            console.group(groupName);
                        }
                        console.debug("Extra Info: " + e.debug + "\nStack Trace:\n" + e.stack);
                        console.groupEnd();
                    }
                    printError(msg);

                    this.updateAnnotations({
                        reason: msg,
                        line: line, col: col,
                        last_line: last_line, last_col: last_col
                    });
                },

                clearAnnotations: function(){
                    this.updateAnnotations(null);
                },

                updateAnnotations: function(res) {
                    let session = editor.getSession();

                    if (res !== null) {
                        session.setAnnotations([{
                            row: res.line,
                            column: res.col,
                            text: res.reason,
                            type: "error",
                            lint: "error"
                        } // TODO add other errors.
                        ]);

                        // marker stores the last hightlight mark or null if none exists
                        if (marker !== null) {
                            session.removeMarker(marker);
                        }
                        let tmp = new Range(res.line, res.col,
                            (res.last_line ? res.last_line : res.line),
                            // highlight the whole line if no end given
                            (res.last_col ? res.last_col : session.getLine(res.line).length));
                        marker = session.addMarker(tmp, "underline_error", "text");
                        //ace_selection
                    } else {
                        // no error, clear old annotations
                        session.clearAnnotations();
                        session.removeMarker(marker);
                        marker = null;
                    }
                },

                setStatus: function(txt) {
                    $('#status').text(txt);
                }
            };
        })();

        //
        // Communication with Worker
        //

        Comm.MainThread.setReceiver(handler);

        // js source code for worker, or null if local
        const cc = Comm.MainThread.getSenderAndReset( worker_enabled ? WORKER_JS : null );

        // reset worker button.
        if (worker_enabled) {
            actionButton("Re-Start Worker: ", "reset",
                "If code does not terminate, you may need to manually reset the worker thread.",
                "RESET");

            $(_RESET_).click(function(event) {
                cc.reset();
                cc.eval(editor.getSession().getValue());
                editor.focus();
            });
        }

        const cursor_elem = $(_CURSOR_);

        function onCursorChange() {
            try {
                const pos = editor.getCursorPosition();
                cursor_elem.html((pos.row + 1) + ":" + pos.column);
                cc.checker(pos);
            } catch (e) {
                // do nothing.
            }
        };

        function onChange(e) {
            // simply re-do everything, ignore diff.
            // more efficient incremental parser left as future work...
            cc.eval(editor.getSession().getValue() );
        };

        editor.selection.on("changeCursor", onCursorChange);
        editor.on("change", onChange);

        // the initial run to parse the example text.
        onChange(null); //trigger dummy change
        // editor apparently automatically gets focused, even without this.
        editor.focus();

    }
};

$(document).ready(Setup.onReady);
