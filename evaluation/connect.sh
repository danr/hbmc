#!/bin/bash
stat remote-web/index.html -t || sshfs danr@remote11.chalmers.se:www/www.cse.chalmers.se/hbmc remote-web
stat remote/.bashrc -t || sshfs danr@ttitania.ce.chalmers.se:. remote
ssh danr@ttitania.ce.chalmers.se
