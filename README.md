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
- Jun. 08: **6/15일은 교수님의 출장 관계로 수업이 없습니다.**
- Jun. 08: Solution이 공개되었습니다.
- Jun. 07: Assignment 6 is uploaded.
- May. 25: Assignment 5 is uploaded.
- May. 19: Assignment 4 is uploaded.
- May. 09: Assignment 3 is uploaded.
- May. 01: Midterm results is uploaded. During the test, there was some misnotification about partial score. So, I checked submitted files manually and gave some partial score to ones didn't get score due to the machine. If you want to check or have any other questions, email TA(sf@sf.snu.ac.kr).
- Apr. 20: [Midterm exam announcement](https://github.com/snu-sf-class/sf202301/blob/main/MidtermInstruction.md)
- Apr. 13: Assignment 2 is uploaded.
- Apr. 12: Midterm will be held on Apr. 30th Sun, 2 - 5 pm
- Mar. 23: Assignment 1 is uploaded.
- Mar. 14: Example code introduced in lecture is uploaded and updated in "lecture" directory

## Assignments

- Download skeleton code and replace `FILL_IN_HERE` with your code in P**.v.
- If you can't complete a proof, just put `Abort.` after `Proof.`
- Please check guidance of each assignment in a submission page.
- **Each assignment have forbidden keyword in forbidden.txt. Try not to use those keywords.**
- **Assignment with dependencies is scored using default skeleton file as dependencies in server. So, using custom definitions in different files not allowed.**
- **Try to finish your proof in one proof environment. Write additional 'Lemma' is not recommended. Use 'assert' tactic instead.**
- Visit http://147.46.245.142:8000 and log-in with your id (e.g. 2016-12345). Your initial password is equivalent to your id.
- Change your password before submitting your assignments.
- If you forget your password, email to ta(sf@sf.snu.ac.kr).
- Use 'make submission' command and attach the zip file.
- No delayed submission.
- Claims: within 2 weeks from the due date, please.

| Due        	 | Description                   	 	 	 	 	 	 	 	 	 	 	 	 	 	    |
|------------	 |---------------------------------------------------------------------------------------
| Apr. 6 23:59   | Assignment 1 - Basic & Induction 	 	 	 	 	 	 	 	 	 	 	 	 	 	|
| Apr. 27 23:59  | Assignment 2 - Lists & Poly & Tactics & Logic	 	 	 	 	 	 	 	 	 	 	|
| May. 23 23:59  | Assignment 3 - IndProp & Imp	 	 	 	 	 	 	 	 	                     	 	|
| Jun. 2 23:59   | Assignment 4 - Equiv & Hoare	 	 	 	 	 	 	 	 	                     	 	|
| Jun. 6 23:59   | Assignment 5 - Hoare2 & HoareAsLogic	 	 	 	 	 	 	 	 	                    |
| Jun. 16 23:59  | Assignment 6 - Smallstep & Types & Stlc & StlcProp & MoreStlc	 	 	 	 	 	 	|

## Grading(tentative)
- Attendance: 5%
- Assignments: 25%
- Mid-term: 30%
- Final: 40%

## Coq

- Install Coq [8.16.1](https://coq.inria.fr).
    + Using an installer (Windows, MacOS)
        * Download [Binaries](https://coq.inria.fr/download) and install it.
        * **Using Coq in Windows could have unexpected, unsupported problem. TA cannot help you in this case.**

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
        
- Tips for those using Windows
    + Using [WSL](https://learn.microsoft.com/ko-kr/windows/wsl/install) allows you work on linux.
    + In WSL, [WSL extension of VS Code](https://learn.microsoft.com/ko-kr/windows/wsl/tutorials/wsl-vscode) is recommended.

## Tactics

- You can look up manuals about [Basic tactics](https://coq.inria.fr/distrib/current/refman/proofs/writing-proofs/index.html), [Automatic solver](https://coq.inria.fr/refman/proofs/automatic-tactics/index.html), and [Ltac](https://coq.inria.fr/refman/proof-engine/ltac.html) for more information about proof techniques.

#### Honor Code: *DO NOT CHEAT*
- Do not copy others' source code, including other students' and resources around the web. Especially, do not consult with public repositories on software foundations.
- Assignment score will be adjusted with the exam score. See above.
