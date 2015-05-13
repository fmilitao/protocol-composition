
/// <reference path='../lib/def/lib.es6.d.ts'/>


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

    class Proxy {

        constructor(
            // proxy function that sends message
            public s: (string, ...any) => void
            ) {
            // intentionally left blank
        }

        dispatch(kind: string, ...args: any[]) {
            this.s(kind, args);
        }

        // arguments.callee.name
    };

    let worker_receiver = null;
    let main_receiver = null;

    export module WorkerThread {

        export interface Sender {
            printError: (string) => void;
            clearAll: () => void;
            errorHandler: (string) => void;
            setStatus: (string) => void;
            println: (string) => void;
            clearAnnotations: () => void;
            updateAnnotations: (any) => void;
            clearTyping: () => void;
            printTyping: (string) => void;
        };

        class SenderObject extends Proxy implements Sender {

            errorHandler(arg: string) {
                super.dispatch('errorHandler', arg);
            }
            clearAll() {
                super.dispatch('clearAll');
            }
            setStatus(arg: string) {
                super.dispatch('setStatus', arg);
            }
            println(arg: string) {
                super.dispatch('println', arg);
            }
            clearAnnotations() {
                super.dispatch('clearAnnotations');
            }
            updateAnnotations(any) { //FIXME this updateANnotations is different from the one used in setup.ts
                super.dispatch('updateAnnotations');
            }
            clearTyping() {
                super.dispatch('clearTyping');
            }
            printTyping(arg: string) {
                super.dispatch('printTyping', arg);
            }
            printError(arg: string) {
                super.dispatch('printError', arg);
            }
        };

        export interface Receiver {
            eval: (string) => void;
            checker: (any) => void;
        };

        export function setReceiver(w: Receiver) {
            worker_receiver = w;
        };

        export function getSender(): SenderObject {
            if (isWorker) {
                let send = function(k, msg) {
                    (<any>self).postMessage({ kind: k, data: msg });
                };

                self.addEventListener('message', function(e) {
                    const m = e.data;
                    try {
                        // this is the 'receiver' var from below
                        WebWorker.receiver[m.kind](m.data);
                    } catch (e) {
                        console.error(e);
                    }
                }, false);

                return new SenderObject(send);
            } else {
                return new SenderObject(function(kind, data) {
                    try {
                        main_receiver[kind](data);
                    } catch (e) {
                        console.error(e);
                    }
                });
            }
        };

    };

    export module MainThread {

        export interface Receiver extends WorkerThread.Sender {
            log: (string) => void;
            debug: (string) => void;
            error: (string) => void;
        };

        export function setReceiver(m : Receiver) {
            main_receiver = m;
        };

        function _getSenderAndReset(WORKER_JS: string): [Function, Function] {
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
                 // assume local

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
                    function(){}
                ];

            }
        };

        export interface MainSenderObject extends WorkerThread.Receiver {
            reset: () => void;
        };

        export function getSenderAndReset(WORKER_JS: string) : MainSenderObject {
            const [send, resetWorker] = _getSenderAndReset(WORKER_JS);

            return {
                eval: function(src : string) {
                    send('eval', src );
                },

                checker: function(p) {
                    send('checker', p);
                },

                reset: function() {
                    resetWorker();
                }
            };
        };

    };

};
