# Software Foundations, SNU M1522.001200, 2023 Spring

- Instructor: Prof. [Chung-Kil Hur](http://sf.snu.ac.kr/gil.hur)
    + Email address: gil.hur@sf.snu.ac.kr
    + Office: 302-426
- TA: [Jaehyung Lee](http://sf.snu.ac.kr/jaehyung.lee)
    + Email address: sf@sf.snu.ac.kr
    + Office: 302-317
- Class material: http://www.cis.upenn.edu/~bcpierce/sf/current/index.html
- Please use email to ask questions (Don't use GitHub Issues)

## Announcements

TBA

## Assignments

TBA

## Grading(tentative)
- Attendance: 5%
- Assignments: 25%
- Mid-term: 30%
- Final: 40%

## Coq

- Install Coq [8.16.1](https://coq.inria.fr).
    + Using an installer (Windows, MacOS)
        * Download [Binaries](https://coq.inria.fr/download) and install it.
        * Using Coq in Windows could have unexpected, unsupported problem. TA cannot help you in this case.

    + Using OPAM (Linux / MacOS) (recommended)
        * OPAM is OCaml package manager, and you can use it to install Coq in Linux.
        * See [https://coq.inria.fr/opam/www/using.html](https://coq.inria.fr/opam/www/using.html).

    + Using brew (MacOS)
        * Run `brew install coq`.
        * Note this wouldn't install CoqIDE.

- Install IDE for Coq.
    + CoqIDE: installed by default.
    + VS Code: [VSCoq](https://github.com/coq-community/vscoq/tree/vscoq1). Follow the setup instructions.
        * In this semester, we will use VS Code as default IDE.
        * This semester is the first try to use VS Code. So, if you have trouble using VSCoq, you can send an email to TA.
        * Basic command (based on vscoq github page)
            * ```alt + down``` : interpret next step
            * ```alt + up``` : return to previous step
            * ```alt + right``` : interpret to right before cursor
            * ```alt + end``` : interpret until end of file
            * ```alt + home``` : reset
            * more commands : ```F1``` & type ```Coq:```
                * example : ```Coq: Prompt Check```
    + Emacs: [Company-Coq](https://github.com/cpitclaudel/company-coq). Follow the setup instructions.
        * If it shows `Searching for program No such file or directory coqtop` error, please add `(custom-set-variables '(coq-prog-name "PATH/TO/coqtop"))` to `.emacs` file.
        * In case of MacOS, coqtop is at `/Applications/CoqIDE_8.9.1.app/Contents/Resources/bin/`.

#### Honor Code: *DO NOT CHEAT*
- Do not copy others' source code, including other students' and resources around the web. Especially, do not consult with public repositories on software foundations.
- Assignment score will be adjusted with the exam score. See above.
