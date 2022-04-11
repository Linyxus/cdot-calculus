This work has been created by adapting the System FSub formalization
(published at https://github.com/charguer/formalmetacoq/tree/master/ln )
created by Arthur Charguéraud. The general structure of the definitions and the
proof is retained in some part, however most of the code has been modified as
the Lambda2Gmu calculus that I have been formalizing differs significantly - I
first removed subtyping to get pure System F and then added tuples and GADTs.
The GADT support required modifying a lot of the infrastructure to support
multiple binders and adding multiple lemmas related to the equational reasoning.

MIT X11 LICENSE
---------------

Copyright (c) 2020 Arthur Charguéraud
Copyright (c) 2021 [Authors of the paper]

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Except as contained in this notice, the name of the copyright holders shall not
be used in advertising or otherwise to promote the sale, use or other dealings
in this Software without prior written authorization from the copyright holders.
