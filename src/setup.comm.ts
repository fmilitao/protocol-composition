
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

    function marshal(e) {
        return JSON.stringify(e);
    };

    function unmarshal(j) {
        return JSON.parse(j);
    };

    function TRY(f: () => void) {
        try {
            f();
        } catch (e) {
            console.error(e);
        }
    }

    class Proxy {

        constructor(
            // proxy function that sends message
            public s: (string, any?) => void
            ) {
            // intentionally left blank
        }

        dispatch(kind: string, args?: any) {
            this.s(kind, args);
        }

        // arguments.callee.name
    };


    export interface WorkerLocal {
        eval( src : string);
        checker( pos : any);
    };

    export interface WorkerRemote extends WorkerLocal {
        reset(); // fork controlling the remote Worker
    };

    export interface EditorRemote {
        printError(msg : string);
        clearAll();
        errorHandler(errors : ErrorWrapper[]);
        
        setStatus(msg : string);
        setErrorStatus(msg: string);
        setOKStatus(msg: string);
        
        println(msg : string);
        clearAnnotations();
        clearTyping();
        printTyping(msg : string);
    };

    export interface EditorLocal extends EditorRemote {
        log( msg : string);
        debug( msg : string);
        error( msg : string);
    };

    // for proxying when local communication is used.
    let local_worker: WorkerLocal = null;
    let local_editor: EditorLocal = null;

    export module WorkerThread {

        class SenderObject extends Proxy implements EditorRemote {

            errorHandler(er: ErrorWrapper[]) {
                super.dispatch('errorHandler', er);
            }
            clearAll() {
                super.dispatch('clearAll');
            }
            setStatus(arg: string) {
                super.dispatch('setStatus', arg);
            }
            setErrorStatus(arg: string) {
                super.dispatch('setErrorStatus', arg);
            }
            setOKStatus(arg: string) {
                super.dispatch('setOKStatus', arg);
            }
            println(arg: string) {
                super.dispatch('println', arg);
            }
            clearAnnotations() {
                super.dispatch('clearAnnotations');
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


        export function setLocalWorker(w: WorkerLocal) {
            local_worker = w;
        };

        export function getRemoteEditor(): EditorRemote {
            if (isWorker) {
                // if remote communication
                self.addEventListener('message', function(e) {
                    TRY(() => local_worker[e.data.kind](e.data.data));
                }, false);

                return new SenderObject(function(k, msg) {
                    TRY(function() {
                        (<any>self).postMessage({
                            kind: k,
                            // only errorHandler needs to (un)marshal argument
                            data: k === 'errorHandler' ? marshal(msg) : msg
                        });
                    });
                });
            } else {
                // if local communication
                return new SenderObject(function(kind, msg) {
                    TRY(() => local_editor[kind](msg));
                });
            }
        };

    };

    export module MainThread {

        export function setLocalEditor(m: EditorLocal) {
            local_editor = m;
        };

        function aux(WORKER_JS: string): [Function, Function] {
            if (WORKER_JS !== null) {
                // if remote communication
                
                let worker: Worker = null;
                
                // launch worker
                function resetWorker() {
                    if (worker !== null) {
                        // stops old worker
                        worker.terminate();
                    }

                    worker = new Worker(WORKER_JS);
                    worker.addEventListener('message', function(e) {
                        TRY(function() {
                            local_editor[e.data.kind](
                                // only errorHandler needs to (un)marshal argument
                                e.data.kind === 'errorHandler' ?
                                    unmarshal(e.data.data) : e.data.data);
                        });
                    }, false);
                };

                resetWorker();

                return [
                    // generic send, tags k as 'kind' and msg as 'data'
                    function(k, msg) {
                        TRY(() => worker.postMessage({ kind: k, data: msg }));
                    },
                    resetWorker
                ];

            } else {
                // if local communication

                return [
                    // send function
                    function(kind, data) {
                        TRY(() => local_worker[kind](data));
                    },
                    // dummy empty reset function
                    function() { }
                ];

            }
        };

        export function getRemoteWorker(WORKER_JS: string): WorkerRemote {
            const [send, resetWorker] = aux(WORKER_JS);

            return {
                eval: function(src: string) {
                    send('eval', src);
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
