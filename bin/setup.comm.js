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
    var worker_receiver = null;
    var main_receiver = null;
    var WorkerThread;
    (function (WorkerThread) {
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
