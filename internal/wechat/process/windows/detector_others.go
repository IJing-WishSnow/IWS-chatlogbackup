//go:build !windows

package windows

import (
	"github.com/shirou/gopsutil/v4/process"
	"github.com/IJing-WishSnow/IWS-chatlogbackup/internal/wechat/model"
)

func initializeProcessInfo(p *process.Process, info *model.Process) error {
	return nil
}
