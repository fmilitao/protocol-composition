// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/
/// <reference path='../lib/def/ace.d.ts' />
/// <reference path='../lib/def/jquery.d.ts' />
/// <reference path='../lib/def/chrome.d.ts' />
var Setup;
(function (Setup) {
    var INFO = "info";
    var EDITOR = "editor";
    var OUTPUT = "output";
    var STATUS_BAR = "statusbar";
    var EXAMPLES = "examples";
    var TYPING = 'typing';
    var TYPEINFO = 'typeinfo';
    var _OUTPUT_ = "#" + OUTPUT;
    var _EXAMPLES_ = "#" + EXAMPLES;
    var _CURSOR_ = "#cursor-position";
    var _TYPEINFO_ = '#' + TYPEINFO;
    var _TYPING_ = '#' + TYPING;
    var _RESET_ = '#reset';
    var WORKER_JS = 'bin/setup.worker.js';
    var DEBUG_MSG = true;
    var worker_enabled = true;
    var default_file = 'examples/welcome.txt';
    var default_style = 'ace/theme/mono_industrial';
    var TYPE_INFO_WIDTHS = null;
    var parameters = document.URL.split('?');
    if (parameters.length > 1) {
        parameters = parameters[1].split('&');
        for (var _i = 0; _i < parameters.length; _i++) {
            var parameter = parameters[_i];
            var tmp = parameter.split('=');
            if (tmp.length > 1) {
                var option = tmp[0];
                var value = tmp[1];
                switch (option) {
                    case 'file':
                        default_file = value;
                        break;
                    case 'style':
                        default_style = value;
                        break;
                    case 'worker':
                        worker_enabled = (value.toLowerCase() === 'true');
                        break;
                    default:
                        console.warn('Ignoring unknown option: ' + parameter);
                        break;
                }
            }
        }
    }
    if (!worker_enabled) {
        function importScript(file) {
            document.write('<script src="' + file + '"><\/script>');
        }
        ;
        console.log('importing scripts to run locally...');
        importScript('lib/jison.js');
        importScript('bin/ast.js');
        importScript('bin/parser.js');
        importScript('bin/typechecker.types.js');
        importScript('bin/typechecker.utils.js');
        importScript('bin/typechecker.js');
        importScript(WORKER_JS);
        console.log('done.');
    }
    function onResize(ev) {
        // note that all these constants must be set through javascript
        // or they will not be accessible to use in these computations.
        // the values are just empirically picked to look OK in chrome.
        var w = window.innerWidth;
        var h = window.innerHeight;
        var controls_height = 20;
        var console_height = 80;
        var split = 270;
        var bar = 35;
        var info = document.getElementById(INFO);
        info.style.width = w + "px";
        info.style.height = bar + "px";
        var editor = document.getElementById(EDITOR);
        editor.style.width = (w) + "px";
        editor.style.height = (h - console_height - controls_height - bar) + "px";
        editor.style.top = bar + "px";
        var controls = document.getElementById(STATUS_BAR);
        controls.style.width = w + "px";
        controls.style.height = (controls_height) + "px";
        controls.style.top = (h - controls_height) + "px";
        var output = document.getElementById(OUTPUT);
        output.style.width = w + "px";
        output.style.height = (console_height) + "px";
        output.style.top = (h - console_height - controls_height) + "px";
        var typing = document.getElementById(TYPING);
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
    }
    ;
    function onReady() {
        $.ajaxSetup({ cache: !DEBUG_MSG });
        if (!window.chrome) {
            document.getElementById("chrome_warn").className = "chrome_show";
        }
        window.onresize = onResize;
        onResize(null);
        var panel = $("#config");
        var entered = false;
        panel.mouseenter(function () {
            entered = true;
        });
        panel.mouseleave(function () {
            if (entered) {
                panel.fadeToggle(50);
                entered = false;
            }
        });
        $("#gear").click(function () {
            var position = $(this).offset();
            var y = position.top;
            var x = position.left;
            panel.css({
                'left': window.innerWidth - (panel.width()) - 15,
                'top': y - 7 + (1.5 * $(this).outerHeight())
            });
            panel.fadeToggle(50);
        });
        var editor = ace.edit(EDITOR);
        editor.$blockScrolling = Infinity;
        var Range = ace.require("ace/range").Range;
        editor.setTheme(default_style);
        var STYLE_LIST = $("#editor-style");
        $.get("lib/ace/ace-themes-list", function (data) {
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
        STYLE_LIST.change(function () {
            var style = $(this).val();
            if (style != '')
                editor.setTheme("ace/" + style);
        });
        editor.getSession().setFoldStyle("manual");
        editor.getSession().setMode("ace/mode/grammar");
        editor.setShowPrintMargin(false);
        editor.getSession().setTabSize(3);
        (function () {
            var setEditor = function (text) {
                editor.selection.removeListener('changeCursor', onCursorChange);
                editor.removeListener('change', onChange);
                editor.getSession().setValue(text);
                editor.focus();
                editor.selection.on("changeCursor", onCursorChange);
                editor.on("change", onChange);
                onChange(null);
            };
            var addExample = function (file, name) {
                name = name.replace('.txt', '');
                var button = $('<span/>', {
                    class: 'b1',
                    text: name,
                    title: 'load example',
                    click: function () {
                        button.addClass('b1_load');
                        $.get(file, function (data) {
                            setEditor(data);
                            button.removeClass('b1_load');
                        });
                    }
                });
                $(_EXAMPLES_).append(button);
            };
            $.get("examples/examples-list", function (data) {
                var examples = data.split('\n');
                for (var i = 0; i < examples.length; ++i) {
                    if (examples[i][0] != '#')
                        addExample('examples/' + examples[i], examples[i]);
                }
            });
            $.get(default_file, function (data) { setEditor(data); });
        })();
        var actionButton = function (label, id, title, text) {
            var ctr = $('#controls');
            ctr.prepend("<div class='action'>" + label + "<button class='exbuttong' id=" + id +
                " title=" + title + "><b>" + text + "</b></button></div>");
        };
        var typeinfo = true;
        (function () {
            actionButton("Typing Information: ", "typeinfo", "Type information is shown when the cursor is placed at the beginning of a construct.", "SHOW");
            var button = $(_TYPEINFO_);
            var panel = $(_TYPING_);
            button.click(function (event) {
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
            panel.click(function () {
                panel.fadeOut('fast');
                editor.focus();
            });
            var t;
            panel.hover(function () {
                window.clearTimeout(t);
                t = window.setTimeout(function () {
                    panel.animate({
                        "left": TYPE_INFO_WIDTHS.minLeft,
                        "max-width": TYPE_INFO_WIDTHS.maxWidth,
                        "width": TYPE_INFO_WIDTHS.maxWidth,
                        "opacity": TYPE_INFO_WIDTHS.maxOpacity
                    }, 'fast');
                }, 500);
            });
            panel.mouseleave(function () {
                window.clearTimeout(t);
                t = window.setTimeout(function () {
                    panel.animate({
                        "left": TYPE_INFO_WIDTHS.defaultLeft,
                        "max-width": TYPE_INFO_WIDTHS.defaultWidth,
                        "width": "auto",
                        "opacity": TYPE_INFO_WIDTHS.defaultOpacity
                    }, 'slow');
                }, 250);
            });
        })();
        var triggers = 'Q';
        var changers = 'q';
        function refreshTypeListners() {
            $('.' + changers)
                .css('background-color', 'inherit')
                .css('outline', 'none');
            $('.' + triggers).hover(function () {
                $(this)
                    .siblings('.' + changers)
                    .css('background-color', 'white')
                    .css('outline', '2px solid #bbbbbb');
            }, function () {
                $(this)
                    .siblings('.' + changers)
                    .css('background-color', 'inherit')
                    .css('outline', 'none');
            });
        }
        ;
        var handle = (function () {
            var o = $(_OUTPUT_);
            var t = $(_TYPING_);
            function clearAll() {
                o.html('');
                clearTyping();
            }
            ;
            function printError(error) {
                println("<span class=bad>" + error + "</span>");
            }
            ;
            function println(val) {
                var old = o.html();
                o.html((old ? old + '\n' : '') + val.toString());
            }
            ;
            function clearTyping() {
                printTyping('');
            }
            ;
            function printTyping(val) {
                if (val == '') {
                    t.hide();
                }
                else {
                    if (typeinfo)
                        t.show();
                }
                t.html(val.toString());
                refreshTypeListners();
            }
            ;
            var marker = null;
            return {
                log: console.log,
                debug: console.debug,
                error: console.error,
                printError: printError,
                clearAll: clearAll,
                println: println,
                clearTyping: clearTyping,
                printTyping: printTyping,
                errorHandler: function (e) {
                    e = JSON.parse(e);
                    var msg = "";
                    var line = 1;
                    var col = 0;
                    var last_line = 1;
                    var last_col = -1;
                    var groupName = null;
                    if (e.hasOwnProperty('ast') && e.ast !== undefined) {
                        line = e.ast.line;
                        col = e.ast.col;
                        last_line = e.ast.last_line;
                        last_col = e.ast.last_col;
                        msg += e.kind + " on line " + (e.ast.line + 1) +
                            (e.ast.col ? (":" + e.ast.col) : '') + " - ";
                    }
                    else {
                        groupName = 'Exception:';
                    }
                    msg += (e.message || e) + ".";
                    if (DEBUG_MSG || groupName != null) {
                        if (groupName == null) {
                            console.groupCollapsed('[Debug-Info] ' + msg);
                        }
                        else {
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
                updateAnnotations: function (res) {
                    var session = editor.getSession();
                    if (res !== null) {
                        session.setAnnotations([{
                                row: res.line,
                                column: res.col,
                                text: res.reason,
                                type: "error",
                                lint: "error"
                            }]);
                        if (marker !== null) {
                            session.removeMarker(marker);
                        }
                        var tmp = new Range(res.line, res.col, (res.last_line ? res.last_line : res.line), (res.last_col ? res.last_col : session.getLine(res.line).length));
                        marker = session.addMarker(tmp, "underline_error", "text");
                    }
                    else {
                        session.clearAnnotations();
                        session.removeMarker(marker);
                        marker = null;
                    }
                },
                setStatus: function (txt) {
                    $('#status').text(txt);
                }
            };
        })();
        var cc = (function () {
            var send, resetWorker;
            Comm.MainThread.setReceiver(handle);
            if (worker_enabled) {
                _a = Comm.MainThread.getSenderAndReset(WORKER_JS), send = _a[0], resetWorker = _a[1];
            }
            else {
                _b = Comm.MainThread.getSenderAndReset(null), send = _b[0], resetWorker = _b[1];
            }
            return {
                eval: function () {
                    send('EVAL', editor.getSession().getValue());
                },
                checker: function (p) {
                    send('CHECKER', p);
                },
                reset: function () {
                    resetWorker();
                    this.eval();
                }
            };
            var _a, _b;
        })();
        if (worker_enabled) {
            actionButton("Re-Start Worker: ", "reset", "If code does not terminate, you may need to manually reset the worker thread.", "RESET");
            var button = $(_RESET_);
            button.click(function (event) {
                cc.reset();
                editor.focus();
            });
        }
        var cursor_elem = $(_CURSOR_);
        function onCursorChange() {
            try {
                var pos = editor.getCursorPosition();
                cursor_elem.html((pos.row + 1) + ":" + pos.column);
                cc.checker(pos);
            }
            catch (e) {
            }
        }
        ;
        function onChange(e) {
            cc.eval();
        }
        ;
        editor.selection.on("changeCursor", onCursorChange);
        editor.on("change", onChange);
        onChange(null);
        editor.focus();
    }
    Setup.onReady = onReady;
})(Setup || (Setup = {}));
;
$(document).ready(Setup.onReady);