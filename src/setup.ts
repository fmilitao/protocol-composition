// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

/// <reference path='../lib/def/ace.d.ts' />
/// <reference path='../lib/def/jquery.d.ts' />
/// <reference path='../lib/def/chrome.d.ts' />

module Setup {

    // this type is only useful further down, but typescript does not let me write it there
    type Annotation = { line: number, col: number, reason: string, last_line: number, last_col: number };

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
    const _RESET_ = '#reset';
    const _CONFIG_ = '#config';
    const _GEAR_ = '#gear';

    const IMPORTS = [
        'lib/jison.js',
        'bin/setup.comm.js',
        'bin/ast.js',
        'bin/parser.js',
        'bin/typechecker.types.js',
        'bin/typechecker.utils.js',
        'bin/typechecker.conformance.js',
        'bin/typechecker.js'];
    const WORKER_JS = 'bin/setup.worker.js';

    let DEBUG_MSG = true;
    let worker_enabled = true;
    let default_file = 'examples/welcome.txt';
    let default_style = 'ace/theme/mono_industrial'; //NOTE: cannot be wrapped in quotes.

    //loads options given as URL parameters
    let parameters = document.URL.split('?');
    if (parameters.length > 1) {
        parameters = parameters[1].split('&');
        for (const parameter of parameters) {
            const tmp = parameter.split('=');
            if (tmp.length > 1) {
                const [option, value] = tmp;
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
        importScript.apply(null, IMPORTS);
        importScript(WORKER_JS);
        console.log('done.');
    }

    let OUTPUT_STYLES;
    // lays all UI components, also useful when resizing window
    function onResize(ev: UIEvent) {
        // note that all these constants must be set through javascript
        // or they will not be accessible to use in these computations.
        // the values are just empirically picked to look OK in chrome.

        const w = window.innerWidth;
        const h = window.innerHeight;

        // all values in pixels
        const controls_h = 20;
        const console_h = 80;
        //let split = 270;
        const top_bar = 35;

        const info = document.getElementById(INFO);
        info.style.width = w + "px";
        info.style.height = top_bar + "px";

        const editor = document.getElementById(EDITOR);
        editor.style.width = (w) + "px";
        editor.style.height = (h - controls_h - top_bar) + "px";
        editor.style.top = top_bar + "px";

        const controls = document.getElementById(STATUS_BAR);
        controls.style.width = w + "px";
        controls.style.height = (controls_h) + "px";
        controls.style.top = (h - controls_h) + "px";

        OUTPUT_STYLES = {
            defaultTop: (h - console_h - controls_h),
            defaultHeight: (console_h),
            maxHeight: (h - controls_h - top_bar)
        };

        const output = document.getElementById(OUTPUT);
        output.style.width = w + "px";
        output.style.height = OUTPUT_STYLES.defaulHeight + "px";
        output.style.top = OUTPUT_STYLES.defaultTop + "px";

    };


    export function onReady() {

        $.ajaxSetup({ cache: !DEBUG_MSG });

        if (!window.chrome) {
            // warn that it is not chrome
            const chrm = $('#chrome_warn');
            chrm.removeClass('chrome_hide');
            chrm.addClass('chrome_show');
            chrm.hover(
                // mouse leave
                function() {
                    chrm.html('⚠ designed for <a href="http://www.google.com/chrome" target= "_blank"> Google Chrome</a>!');
                },
                // mouse enter
                function() {
                    chrm.html('⚠');
                });

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

        const panel = $(_CONFIG_);
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

        $(_GEAR_).click(function() {

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


        // ace editor's type is not complete, must restort to 'any'
        const editor: any = ace.edit(EDITOR);
        editor.$blockScrolling = Infinity; // This is necessary to remove warning.
        const Range = ace.require("ace/range").Range;

        //
        // theme selector
        //

        editor.setTheme(default_style);
        // selected="selected"
        const STYLE_LIST = $("#editor-style");
        $.get("lib/ace/ace-themes-list", function(data) {
            const themes = data.split('\n');
            for (let i = 0; i < themes.length; ++i) {
                let name = themes[i];
                name = name.replace('-', '/');
                name = name.replace('.js', '');
                const option = $('<option/>', {
                    value: name,
                    text: name
                });
                STYLE_LIST.append(option);
            }
        });

        STYLE_LIST.change(function() {
            const style = $(this).val();
            if (style != '')
                editor.setTheme("ace/" + style);
        });

        // disables code folding
        editor.getSession().setFoldStyle("manual");
        editor.getSession().setMode("ace/mode/grammar");
        editor.setShowPrintMargin(false);
        editor.getSession().setTabSize(3);

        //
        // Examples buttons.
        //

        function setEditor(text) {
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
            onChange();
        };

        function addExample(file, name) {
            name = name.replace('.txt', '');
            const button = $('<span/>', {
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
        };

        $.get("examples/examples-list", function(data) {
            const examples = data.split('\n');
            for (let i = 0; i < examples.length; ++i) {
                if (examples[i][0] != '#') // ignore commented stuff
                    addExample('examples/' + examples[i], examples[i]);
            }
        });

        // setup editor with default file.
        $.get(default_file, function(data) { setEditor(data); });


        //
        // Action buttons.
        //

        function actionButton(label, id, title, text) {
            $('#controls').prepend("<div class='action'>" + label + "<button class='exbuttong' id=" + id +
                " title=" + title + "><b>" + text + "</b></button></div>");
        };

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
            //const t = $(_TYPING_);
            const $status = $('#status');
            const OK_CLASS = 'ok_status';
            const ER_CLASS = 'error_status';

            // if I do not do this, then the first showing of 'o' is too short
            // if the element requires less than defaultHeight to show correctly
            o.animate({
                "top": OUTPUT_STYLES.defaultTop + "px",
                "height": OUTPUT_STYLES.defaultHeight + "px",
            }, 0);
            o.attr('title', 'click to close');
            o.click(function() {
                o.hide();
                editor.focus();
            });

            //----
            let t;
            o.hover(function() {

                const top = Math.min(
                    OUTPUT_STYLES.defaultTop + (OUTPUT_STYLES.defaultHeight - o[0].scrollHeight),
                    OUTPUT_STYLES.maxHeight
                    );

                const s = o[0].scrollHeight < OUTPUT_STYLES.defaultHeight ?
                    // if scrollHeight too small
                    OUTPUT_STYLES.defaultHeight :
                    // if scrollHeight too large
                    Math.min(OUTPUT_STYLES.maxHeight, o[0].scrollHeight);

                window.clearTimeout(t);
                t = window.setTimeout(function() {
                    o.animate({
                        "top": Math.min(top, OUTPUT_STYLES.defaultTop) + "px",
                        'height': s + 'px'
                    }, 'fast');
                }, 500);
            });
            o.mouseleave(function() {

                window.clearTimeout(t);
                t = window.setTimeout(function() {
                    o.animate({
                        "top": OUTPUT_STYLES.defaultTop + "px",
                        "height": OUTPUT_STYLES.defaultHeight + "px",
                    }, 'fast');
                }, 250);
            });
            // ------

            // aux functions
            function clearAll() {
                o.html('');
                o.hide();
            };

            function printError(error) {
                // uses inner span to print with different colors
                println("<span class=bad>" + error + "</span>");
            };

            function println(val) {
                let old = o.html();
                o.html((old ? old + '\n' : '') + val.toString());
                refreshTypeListners();
                o.show();
            };

            let marker = [];
            function updateAnnotations(a: Annotation[]) {
                const session = editor.getSession();

                // marker stores the last hightlight mark or null if none exists
                if (marker.length !== 0) {
                    for (const m of marker) {
                        session.removeMarker(m);
                    }
                    marker = [];
                }
                
                // clears old annotations
                if (a === null) {
                    session.clearAnnotations();
                    return;
                }

                const aux = a.map(
                    function(i: Annotation) {
                        return {
                            row: i.line,
                            column: i.col,
                            text: i.reason,
                            type: "error",
                            lint: "error"
                        };
                    });
                session.setAnnotations(aux);

                for (const r of a) {
                    // underline error text, full line if no last col/line given.
                    const range = new Range(r.line, r.col,
                        (r.last_line ? r.last_line : r.line),
                        // highlight the whole line if no end given
                        (r.last_col ? r.last_col : session.getLine(r.line).length));
                    marker.push(session.addMarker(range, "underline_error", "text"));
                }

            };

            return {

                // note that wrapping function is need because of 'this' in 'log', etc.
                log: function(msg: string) { console.log(msg); },
                debug: function(msg: string) { console.debug(msg); },
                error: function(msg: string) { console.error(msg); },

                //
                // info
                //

                printError: printError,
                clearAll: clearAll,
                println: println,

                //
                // error handling & annotaitons
                //

                // WARNING: assumes JSONed object
                errorHandler: function(es: ErrorWrapper[]) {
                    let annotations: Annotation[] = [];
                    for (const e of es) {
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
                        // this actually adds up the error messages
                        printError(msg);

                        // must group annotations before showing.
                        annotations.push({
                            reason: msg,
                            line: line, col: col,
                            last_line: last_line, last_col: last_col
                        });
                    }

                    updateAnnotations(annotations);
                },

                clearAnnotations: function() {
                    updateAnnotations(null);
                },

                setStatus: function(txt) {
                    $status.removeClass(OK_CLASS);
                    $status.removeClass(ER_CLASS);
                    $status.text(txt);
                },

                setOKStatus: function(txt) {
                    $status.removeClass(ER_CLASS);
                    $status.addClass(OK_CLASS);
                    $status.text(txt);
                },

                setErrorStatus: function(txt) {
                    $status.removeClass(OK_CLASS);
                    $status.addClass(ER_CLASS);
                    $status.text(txt);
                }

            };
        })();

        //
        // Communication with Worker
        //

        Comm.MainThread.setLocalEditor(handler);

        // js source code for worker, or null if local
        const cc = Comm.MainThread.getRemoteWorker(worker_enabled ? WORKER_JS : null);

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

        function onChange(event?) {
            // simply re-do everything, ignore diff.
            // more efficient incremental parser left as future work...
            cc.eval(editor.getSession().getValue());
        };

        editor.selection.on("changeCursor", onCursorChange);
        editor.on("change", onChange);

        // the initial run to parse the example text.
        onChange(); //trigger dummy change
        // editor apparently automatically gets focused, even without this.
        editor.focus();

    }
};

$(document).ready(Setup.onReady);
