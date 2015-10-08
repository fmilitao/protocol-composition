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
    var _RESET_ = '#reset';
    var _CONFIG_ = '#config';
    var _GEAR_ = '#gear';
    var IMPORTS = [
        'lib/jison.js',
        'bin/setup.comm.js',
        'bin/ast.js',
        'bin/parser.js',
        'bin/typechecker.types.js',
        'bin/typechecker.utils.js',
        'bin/typechecker.conformance.js',
        'bin/typechecker.js'];
    var WORKER_JS = 'bin/setup.worker.js';
    var DEBUG_MSG = true;
    var worker_enabled = true;
    var default_file = 'examples/welcome.txt';
    var default_style = 'ace/theme/mono_industrial';
    var parameters = document.URL.split('?');
    if (parameters.length > 1) {
        parameters = parameters[1].split('&');
        for (var _i = 0; _i < parameters.length; _i++) {
            var parameter = parameters[_i];
            var tmp = parameter.split('=');
            if (tmp.length > 1) {
                var option = tmp[0], value = tmp[1];
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
        console.log('importing scripts to run locally...');
        importScript.apply(null, IMPORTS);
        importScript(WORKER_JS);
        console.log('done.');
    }
    var OUTPUT_STYLES;
    function onResize(ev) {
        // note that all these constants must be set through javascript
        // or they will not be accessible to use in these computations.
        // the values are just empirically picked to look OK in chrome.
        var w = window.innerWidth;
        var h = window.innerHeight;
        var controls_h = 20;
        var console_h = 80;
        var top_bar = 35;
        var info = document.getElementById(INFO);
        info.style.width = w + "px";
        info.style.height = top_bar + "px";
        var editor = document.getElementById(EDITOR);
        editor.style.width = (w) + "px";
        editor.style.height = (h - controls_h - top_bar) + "px";
        editor.style.top = top_bar + "px";
        var controls = document.getElementById(STATUS_BAR);
        controls.style.width = w + "px";
        controls.style.height = (controls_h) + "px";
        controls.style.top = (h - controls_h) + "px";
        OUTPUT_STYLES = {
            defaultTop: (h - console_h - controls_h),
            defaultHeight: (console_h),
            maxHeight: (h - controls_h - top_bar)
        };
        var output = document.getElementById(OUTPUT);
        output.style.width = w + "px";
        output.style.height = OUTPUT_STYLES.defaulHeight + "px";
        output.style.top = OUTPUT_STYLES.defaultTop + "px";
    }
    ;
    function onReady() {
        $.ajaxSetup({ cache: !DEBUG_MSG });
        if (!window.chrome) {
            var chrm = $('#chrome_warn');
            chrm.removeClass('chrome_hide');
            chrm.addClass('chrome_show');
            chrm.hover(function () {
                chrm.html('⚠ designed for <a href="http://www.google.com/chrome" target= "_blank"> Google Chrome</a>!');
            }, function () {
                chrm.html('⚠');
            });
        }
        window.onresize = onResize;
        onResize(null);
        var panel = $(_CONFIG_);
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
        $(_GEAR_).click(function () {
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
                var name_1 = themes[i];
                name_1 = name_1.replace('-', '/');
                name_1 = name_1.replace('.js', '');
                var option = $('<option/>', {
                    value: name_1,
                    text: name_1
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
        function setEditor(text) {
            editor.selection.removeListener('changeCursor', onCursorChange);
            editor.removeListener('change', onChange);
            editor.getSession().setValue(text);
            editor.focus();
            editor.selection.on("changeCursor", onCursorChange);
            editor.on("change", onChange);
            onChange();
        }
        ;
        function addExample(file, name) {
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
        }
        ;
        $.get("examples/examples-list", function (data) {
            var examples = data.split('\n');
            for (var i = 0; i < examples.length; ++i) {
                if (examples[i][0] != '#')
                    addExample('examples/' + examples[i], examples[i]);
            }
        });
        $.get(default_file, function (data) { setEditor(data); });
        function actionButton(label, id, title, text) {
            $('#controls').prepend("<div class='action'>" + label + "<button class='exbuttong' id=" + id +
                " title=" + title + "><b>" + text + "</b></button></div>");
        }
        ;
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
        var handler = (function () {
            var o = $(_OUTPUT_);
            var $status = $('#status');
            var OK_CLASS = 'ok_status';
            var ER_CLASS = 'error_status';
            o.animate({
                "top": OUTPUT_STYLES.defaultTop + "px",
                "height": OUTPUT_STYLES.defaultHeight + "px",
            }, 0);
            o.attr('title', 'click to close');
            o.click(function () {
                o.hide();
                editor.focus();
            });
            var t;
            o.hover(function () {
                var top = Math.min(OUTPUT_STYLES.defaultTop + (OUTPUT_STYLES.defaultHeight - o[0].scrollHeight), OUTPUT_STYLES.maxHeight);
                var s = o[0].scrollHeight < OUTPUT_STYLES.defaultHeight ?
                    OUTPUT_STYLES.defaultHeight :
                    Math.min(OUTPUT_STYLES.maxHeight, o[0].scrollHeight);
                window.clearTimeout(t);
                t = window.setTimeout(function () {
                    o.animate({
                        "top": Math.min(top, OUTPUT_STYLES.defaultTop) + "px",
                        'height': s + 'px'
                    }, 'fast');
                }, 500);
            });
            o.mouseleave(function () {
                window.clearTimeout(t);
                t = window.setTimeout(function () {
                    o.animate({
                        "top": OUTPUT_STYLES.defaultTop + "px",
                        "height": OUTPUT_STYLES.defaultHeight + "px",
                    }, 'fast');
                }, 250);
            });
            function clearAll() {
                o.html('');
                o.hide();
            }
            ;
            function printError(error) {
                println("<span class=bad>" + error + "</span>");
            }
            ;
            function println(val) {
                var old = o.html();
                o.html((old ? old + '\n' : '') + val.toString());
                refreshTypeListners();
                o.show();
            }
            ;
            var marker = [];
            function updateAnnotations(a) {
                var session = editor.getSession();
                if (marker.length !== 0) {
                    for (var _i = 0; _i < marker.length; _i++) {
                        var m = marker[_i];
                        session.removeMarker(m);
                    }
                    marker = [];
                }
                if (a === null) {
                    session.clearAnnotations();
                    return;
                }
                var aux = a.map(function (i) {
                    return {
                        row: i.line,
                        column: i.col,
                        text: i.reason,
                        type: "error",
                        lint: "error"
                    };
                });
                session.setAnnotations(aux);
                for (var _a = 0; _a < a.length; _a++) {
                    var r = a[_a];
                    var range = new Range(r.line, r.col, (r.last_line ? r.last_line : r.line), (r.last_col ? r.last_col : session.getLine(r.line).length));
                    marker.push(session.addMarker(range, "underline_error", "text"));
                }
            }
            ;
            return {
                log: function (msg) { console.log(msg); },
                debug: function (msg) { console.debug(msg); },
                error: function (msg) { console.error(msg); },
                printError: printError,
                clearAll: clearAll,
                println: println,
                errorHandler: function (es) {
                    var annotations = [];
                    for (var _i = 0; _i < es.length; _i++) {
                        var e = es[_i];
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
                        annotations.push({
                            reason: msg,
                            line: line, col: col,
                            last_line: last_line, last_col: last_col
                        });
                    }
                    updateAnnotations(annotations);
                },
                clearAnnotations: function () {
                    updateAnnotations(null);
                },
                setStatus: function (txt) {
                    $status.removeClass(OK_CLASS);
                    $status.removeClass(ER_CLASS);
                    $status.text(txt);
                },
                setOKStatus: function (txt) {
                    $status.removeClass(ER_CLASS);
                    $status.addClass(OK_CLASS);
                    $status.text(txt);
                },
                setErrorStatus: function (txt) {
                    $status.removeClass(OK_CLASS);
                    $status.addClass(ER_CLASS);
                    $status.text(txt);
                }
            };
        })();
        Comm.MainThread.setLocalEditor(handler);
        var cc = Comm.MainThread.getRemoteWorker(worker_enabled ? WORKER_JS : null);
        if (worker_enabled) {
            actionButton("Re-Start Worker: ", "reset", "If code does not terminate, you may need to manually reset the worker thread.", "RESET");
            $(_RESET_).click(function (event) {
                cc.reset();
                cc.eval(editor.getSession().getValue());
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
        function onChange(event) {
            cc.eval(editor.getSession().getValue());
        }
        ;
        editor.selection.on("changeCursor", onCursorChange);
        editor.on("change", onChange);
        onChange();
        editor.focus();
    }
    Setup.onReady = onReady;
})(Setup || (Setup = {}));
;
$(document).ready(Setup.onReady);
//# sourceMappingURL=setup.js.map