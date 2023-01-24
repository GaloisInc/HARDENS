;;   Copyright 2021, 2022, 2023 Galois, Inc.
;;
;;   Licensed under the Apache License, Version 2.0 (the "License");
;;   you may not use this file except in compliance with the License.
;;   You may obtain a copy of the License at
;;
;;       http://www.apache.org/licenses/LICENSE-2.0
;;
;;   Unless required by applicable law or agreed to in writing, software
;;   distributed under the License is distributed on an "AS IS" BASIS,
;;   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;;   See the License for the specific language governing permissions and
;;   limitations under the License.

;; ===== lando mode
(defvar lando-mode-hook nil)
(defvar lando-mode-map
  (let ((lando-mode-map (make-keymap)))
    (define-key lando-mode-map "\C-j" 'newline-and-indent)
    lando-mode-map)
  "Keymap for LANDO major mode")

(add-to-list 'auto-mode-alist '("\\.lando\\'" . lando-mode))

(defconst lando-font-lock-keywords-1
  (list 
   '("\\<system\\>" . font-lock-builtin-face)
   '("\\<subsystem\\>" . font-lock-builtin-face)
   '("\\<component\\>" . font-lock-builtin-face)
   '("\\<events\\>" . font-lock-builtin-face)
   '("\\<scenarios\\>" . font-lock-builtin-face)
   '("\\<requirements\\>" . font-lock-builtin-face)
   '("\\<relation\\>" . font-lock-builtin-face)
   '("\\<indexing\\>" . font-lock-builtin-face)
   '("\\<inherit\\>" . font-lock-builtin-face)
   '("\\<client\\>" . font-lock-builtin-face)
   '("\\<contains\\>" . font-lock-builtin-face)
  ) 
  "Minimal highlighting expressions for LANDO mode.")

(defvar lando-font-lock-keywords lando-font-lock-keywords-1 "Default highlighting expressions for LANDO mode.")

(defun lando-mode ()
  (interactive)
  (kill-all-local-variables)
  (use-local-map lando-mode-map)
  ;; Set up font-lock
  (set (make-local-variable 'font-lock-defaults) '(lando-font-lock-keywords))
  (setq major-mode 'lando-mode)
  (setq mode-name "LANDO")
  (run-hooks 'lando-mode-hook))

(provide 'lando-mode)
;; ===== end of lando-mode
