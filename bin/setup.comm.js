/// <reference path='../lib/def/lib.es6.d.ts'/>
var __extends = this.__extends || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    __.prototype = b.prototype;
    d.prototype = new __();
};
if (typeof (importScripts) === 'undefined') {
    function importScript() {
        var files = [];
        for (var _i = 0; _i < arguments.length; _i++) {
            files[_i - 0] = arguments[_i];
        }
        for (var _a = 0; _a < files.length; _a++) {
            var file = files[_a];
            document.write('<script src="' + file + '"><\/script>');
        }
    }
    ;
}
var Comm;
(function (Comm) {
    function marshal(e) {
        return JSON.stringify(e);
    }
    ;
    function unmarshal(j) {
        return JSON.parse(j);
    }
    ;
    function TRY(f) {
        try {
            f();
        }
        catch (e) {
            console.error(e);
        }
    }
    var Proxy = (function () {
        function Proxy(s) {
            this.s = s;
        }
        Proxy.prototype.dispatch = function (kind, args) {
            this.s(kind, args);
        };
        return Proxy;
    })();
    ;
    ;
    ;
    ;
    ;
    var local_worker = null;
    var local_editor = null;
    var WorkerThread;
    (function (WorkerThread) {
        var SenderObject = (function (_super) {
            __extends(SenderObject, _super);
            function SenderObject() {
                _super.apply(this, arguments);
            }
            SenderObject.prototype.errorHandler = function (er) {
                _super.prototype.dispatch.call(this, 'errorHandler', er);
            };
            SenderObject.prototype.clearAll = function () {
                _super.prototype.dispatch.call(this, 'clearAll');
            };
            SenderObject.prototype.setStatus = function (arg) {
                _super.prototype.dispatch.call(this, 'setStatus', arg);
            };
            SenderObject.prototype.setErrorStatus = function (arg) {
                _super.prototype.dispatch.call(this, 'setErrorStatus', arg);
            };
            SenderObject.prototype.setOKStatus = function (arg) {
                _super.prototype.dispatch.call(this, 'setOKStatus', arg);
            };
            SenderObject.prototype.println = function (arg) {
                _super.prototype.dispatch.call(this, 'println', arg);
            };
            SenderObject.prototype.clearAnnotations = function () {
                _super.prototype.dispatch.call(this, 'clearAnnotations');
            };
            SenderObject.prototype.printError = function (arg) {
                _super.prototype.dispatch.call(this, 'printError', arg);
            };
            return SenderObject;
        })(Proxy);
        ;
        function setLocalWorker(w) {
            local_worker = w;
        }
        WorkerThread.setLocalWorker = setLocalWorker;
        ;
        function getRemoteEditor() {
            if (isWorker) {
                self.addEventListener('message', function (e) {
                    TRY(function () { return local_worker[e.data.kind](e.data.data); });
                }, false);
                return new SenderObject(function (k, msg) {
                    TRY(function () {
                        self.postMessage({
                            kind: k,
                            data: k === 'errorHandler' ? marshal(msg) : msg
                        });
                    });
                });
            }
            else {
                return new SenderObject(function (kind, msg) {
                    TRY(function () { return local_editor[kind](msg); });
                });
            }
        }
        WorkerThread.getRemoteEditor = getRemoteEditor;
        ;
    })(WorkerThread = Comm.WorkerThread || (Comm.WorkerThread = {}));
    ;
    var MainThread;
    (function (MainThread) {
        function setLocalEditor(m) {
            local_editor = m;
        }
        MainThread.setLocalEditor = setLocalEditor;
        ;
        function aux(WORKER_JS) {
            if (WORKER_JS !== null) {
                var worker = null;
                function resetWorker() {
                    if (worker !== null) {
                        worker.terminate();
                    }
                    worker = new Worker(WORKER_JS);
                    worker.addEventListener('message', function (e) {
                        TRY(function () {
                            local_editor[e.data.kind](e.data.kind === 'errorHandler' ?
                                unmarshal(e.data.data) : e.data.data);
                        });
                    }, false);
                }
                ;
                resetWorker();
                return [
                    function (k, msg) {
                        TRY(function () { return worker.postMessage({ kind: k, data: msg }); });
                    },
                    resetWorker
                ];
            }
            else {
                return [
                    function (kind, data) {
                        TRY(function () { return local_worker[kind](data); });
                    },
                    function () { }
                ];
            }
        }
        ;
        function getRemoteWorker(WORKER_JS) {
            var _a = aux(WORKER_JS), send = _a[0], resetWorker = _a[1];
            return {
                eval: function (src) {
                    send('eval', src);
                },
                checker: function (p) {
                    send('checker', p);
                },
                reset: function () {
                    resetWorker();
                }
            };
        }
        MainThread.getRemoteWorker = getRemoteWorker;
        ;
    })(MainThread = Comm.MainThread || (Comm.MainThread = {}));
    ;
})(Comm || (Comm = {}));
;
