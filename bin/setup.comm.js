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
                var send_1 = function (k, msg) {
                    self.postMessage({ kind: k, data: msg });
                };
                self.addEventListener('message', function (e) {
                    var m = e.data;
                    try {
                        receiver[m.kind](m.data);
                    }
                    catch (e) {
                        console.error(e);
                    }
                }, false);
                return send_1;
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
                var send_2;
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
                    send_2 = function (k, msg) {
                        worker.postMessage({ kind: k, data: msg });
                    };
                }
                ;
                resetWorker();
                return [send_2, resetWorker];
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
