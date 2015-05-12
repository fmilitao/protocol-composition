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
    var Proxy = (function () {
        function Proxy(s) {
            this.s = s;
        }
        Proxy.prototype.dispatch = function (m) {
            var args = [];
            for (var _i = 1; _i < arguments.length; _i++) {
                args[_i - 1] = arguments[_i];
            }
            this.s(m, args);
        };
        return Proxy;
    })();
    ;
    var worker_receiver = null;
    var main_receiver = null;
    var WorkerThread;
    (function (WorkerThread) {
        var SenderObject = (function (_super) {
            __extends(SenderObject, _super);
            function SenderObject() {
                _super.apply(this, arguments);
            }
            SenderObject.prototype.errorHandler = function () {
                _super.prototype.dispatch.call(this, arguments.callee.name);
            };
            SenderObject.prototype.clearAll = function () {
                _super.prototype.dispatch.call(this, arguments.callee.name);
            };
            SenderObject.prototype.setStatus = function () {
                _super.prototype.dispatch.call(this, arguments.callee.name);
            };
            SenderObject.prototype.println = function () {
                _super.prototype.dispatch.call(this, arguments.callee.name);
            };
            SenderObject.prototype.updateAnnotations = function () {
                _super.prototype.dispatch.call(this, arguments.callee.name);
            };
            SenderObject.prototype.clearTyping = function () {
                _super.prototype.dispatch.call(this, arguments.callee.name);
            };
            SenderObject.prototype.printTyping = function () {
                _super.prototype.dispatch.call(this, arguments.callee.name);
            };
            return SenderObject;
        })(Proxy);
        ;
        function setReceiver(w) {
            worker_receiver = w;
        }
        WorkerThread.setReceiver = setReceiver;
        ;
        function getSender() {
            if (isWorker) {
                var send = function (k, msg) {
                    self.postMessage({ kind: k, data: msg });
                };
                self.addEventListener('message', function (e) {
                    var m = e.data;
                    try {
                        WebWorker.receiver[m.kind](m.data);
                    }
                    catch (e) {
                        console.error(e);
                    }
                }, false);
                return send;
            }
            else {
                return function (kind, data) {
                    try {
                        main_receiver[kind](data);
                    }
                    catch (e) {
                        console.error(e);
                    }
                };
            }
        }
        WorkerThread.getSender = getSender;
        ;
    })(WorkerThread = Comm.WorkerThread || (Comm.WorkerThread = {}));
    ;
    var MainThread;
    (function (MainThread) {
        function setReceiver(m) {
            main_receiver = m;
        }
        MainThread.setReceiver = setReceiver;
        ;
        function getSenderAndReset(WORKER_JS) {
            if (WORKER_JS !== null) {
                var worker = null;
                var send;
                function resetWorker() {
                    if (worker !== null) {
                        worker.terminate();
                    }
                    worker = new Worker(WORKER_JS);
                    worker.addEventListener('message', function (e) {
                        var m = e.data;
                        try {
                            main_receiver[m.kind](m.data);
                        }
                        catch (er) {
                            console.error(er);
                        }
                    }, false);
                    send = function (k, msg) {
                        worker.postMessage({ kind: k, data: msg });
                    };
                }
                ;
                resetWorker();
                return [send, resetWorker];
            }
            else {
                return [
                    function (kind, data) {
                        try {
                            worker_receiver[kind](data);
                        }
                        catch (e) {
                            console.error(e);
                        }
                    },
                    function () { }
                ];
            }
        }
        MainThread.getSenderAndReset = getSenderAndReset;
        ;
    })(MainThread = Comm.MainThread || (Comm.MainThread = {}));
    ;
})(Comm || (Comm = {}));
;
