
#Protocol Conformance Checker#

Grammar is limited to only check 'equals', 'subtype' and 'share' (and substitution).
Instead of recursion, we have 'typedef' for clarity.

NOTE: We currently do not enforce all well-formedness conditions on types. If a type is not well-formed the algorithm may not terminate.

(Work in progress... not done.)

#FIXMES#

* missing failure tests on conformance on 'test2.txt'

* FIX on keyF that creates key to table cycles in the types, needs to consider environment due to bounded quantification.


- define error constants/enum instead of having constants spread out through the code.

- use 'const' keyword for constants. Note that some browsers may not support this. However, our target is Google Chrome which does support 'const'. See: http://kangax.github.io/compat-table/es6/

- JS tips: http://bonsaiden.github.io/JavaScript-Garden/

- cool transitions: https://github.com/IanLunn/Hover


##Extra Credits##

- Types and Programming Languages, Chapter 6 (for De Bruijn stuff).
- Subtyping Recursive Types, for recursion checks.


## Useful Notes ##

  * Use `?file=PATH` to load file in repo, even if not listed as example.
  * `?worker=false` to run locally instead of on Web Worker. Multiple arguments should be `&` separated, such as `?file=PATH&worker=false`.
  * [Chrome Console](https://developers.google.com/chrome-developer-tools/docs/console) useful for debugging.
  * [JS style guide](http://google-styleguide.googlecode.com/svn/trunk/javascriptguide.xml)
  * [Ace](http://ace.ajax.org/tool/mode_creator.html) style fix helper.
  * fix drop down list style with [this](http://danielneumann.com/blog/how-to-style-dropdown-with-css-only/) and [this](http://stackoverflow.com/questions/1337149/how-do-i-style-form-drop-down-lists).
  * [Identity versus equality in JS](http://stackoverflow.com/questions/359494/does-it-matter-which-equals-operator-vs-i-use-in-javascript-comparisons).
  * [Chrome Debugging](https://developers.google.com/chrome-developer-tools/docs/javascript-debugging)
  * [LINK](https://developers.google.com/chrome-developer-tools/docs/heap-profiling) [LINK](https://developers.google.com/speed/articles/optimizing-javascript) profiling and optimization.
  * http://stackoverflow.com/questions/1964839/jquery-please-wait-loading-animation
