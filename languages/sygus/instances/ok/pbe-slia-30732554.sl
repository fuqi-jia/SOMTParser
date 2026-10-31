(set-logic SLIA)

(synth-fun f ((_arg_0 String)) String
    ((Start String (ntString))
    (ntString String (_arg_0 "" " " "|" (str.++ ntString ntString) (str.replace ntString ntString ntString) (str.at ntString ntInt) (int.to.str ntInt) (ite ntBool ntString ntString) (str.substr ntString ntInt ntInt)))
    (ntInt Int (1 0 -1 (+ ntInt ntInt) (- ntInt ntInt) (str.len ntString) (str.to.int ntString) (ite ntBool ntInt ntInt) (str.indexof ntString ntString ntInt)))
    (ntBool Bool (true false (= ntInt ntInt) (str.prefixof ntString ntString) (str.suffixof ntString ntString) (str.contains ntString ntString)))))

(constraint (= (f "TL-18273982| 10MM") "TL-18273982"))
(constraint (= (f "TL-288762| 76DK") "TL-288762"))
(constraint (= (f "CT-576") "CT-576"))
(constraint (= (f "N/A") "N/A"))

(check-synth)

