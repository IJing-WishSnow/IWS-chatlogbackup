package main

import (
	"log"

	"github.com/IJing-WishSnow/IWS-chatlogbackup/cmd/chatlog"
)

func main() {
	log.SetFlags(log.LstdFlags | log.Lshortfile)
	chatlog.Execute()
}
