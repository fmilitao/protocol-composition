
if (typeof (importScripts) === 'undefined') {
    // defines importScript function for local loading
    function importScript(...files: string[]) {
        for (let file of files) {
            document.write('<script src="' + file + '"><\/script>');
        }
    };
}

//
// Communication Module
//
module Comm {

    let worker_receiver = null;
    let main_receiver = null;

    export module WorkerThread {

        export function setReceiver(w) {
            worker_receiver = w;
        };

        export function getSender() {
            if (isWorker) {
                let send = function(k, msg) {
                    (<any>self).postMessage({ kind: k, data: msg });
                };

                self.addEventListener('message', function(e) {
                    const m = e.data;
                    try {
                        // this is the 'receiver' var from below
                        receiver[m.kind](m.data);
                    } catch (e) {
                        console.error(e);
                    }
                }, false);

                return send;
            } else {
                return function(kind, data) {
                    try {
                        main_receiver[kind](data);
                    } catch (e) {
                        console.error(e);
                    }
                };
            }
        };

    };

    export module MainThread {

        export function setReceiver(m) {
            main_receiver = m;
        };

        export function getSenderAndReset(WORKER_JS: string): [Function, Function] {
            if (WORKER_JS !== null) {

                let worker: Worker = null;
                let send: Function;

                // launch worker
                function resetWorker() {
                    if (worker !== null) {
                        // stops old worker
                        worker.terminate();
                    }

                    worker = new Worker(WORKER_JS);
                    worker.addEventListener('message', function(e) {
                        var m = e.data;
                        try {
                            main_receiver[m.kind](m.data);
                        } catch (er) {
                            console.error(er);
                        }
                    }, false);

                    // generic send, tags k as 'kind' and msg as 'data'
                    send = function(k, msg) {
                        worker.postMessage({ kind: k, data: msg });
                    };
                };

                resetWorker();

                return [send, resetWorker];

            } else {

                return [
                    // send function
                    function(kind, data) {
                        try {
                            worker_receiver[kind](data);
                        } catch (e) {
                            console.error(e);
                        }
                    },
                    // dummy empty reset function
                    () => { }
                ];

            }
        };

    };

};
