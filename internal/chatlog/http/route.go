package http

import (
	"context"
	"embed"
	"encoding/csv"
	"encoding/json"
	"fmt"
	"html/template"
	"io"
	"io/fs"
	"math"
	"net/http"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"time"

	"github.com/gin-gonic/gin"
	"github.com/rs/zerolog/log"

	"github.com/IJing-WishSnow/IWS-chatlogbackup/internal/errors"
	"github.com/IJing-WishSnow/IWS-chatlogbackup/internal/model"
	"github.com/IJing-WishSnow/IWS-chatlogbackup/pkg/util"
	"github.com/IJing-WishSnow/IWS-chatlogbackup/pkg/util/dat2img"
	"github.com/IJing-WishSnow/IWS-chatlogbackup/pkg/util/silk"
)

//go:embed static
var EFS embed.FS

// 统一的 HTML 预览组件片段
var previewHTMLSnippetBase = `
<style>#preview{position:fixed;top:60px;left:40px;z-index:9999;display:none;background:#1f2329;border:1px solid #444;padding:4px 4px 8px;border-radius:8px;max-width:720px;max-height:520px;box-shadow:0 4px 16px rgba(0,0,0,0.45);color:#eee;font-size:12px;resize:both;overflow:hidden;}#preview.dragging{opacity:.85;cursor:grabbing;}#preview .pv-header{display:flex;align-items:center;justify-content:space-between;gap:6px;margin:0 2px 4px 2px;font-size:12px;user-select:none;cursor:grab;}#preview .pv-header .title{flex:1;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;color:#9ecbff;font-weight:600;}#preview button{background:#2d333b;border:1px solid #555;color:#ddd;font-size:11px;padding:2px 6px;border-radius:4px;cursor:pointer;}#preview button:hover{background:#3a424b}#preview-content{max-width:100%;max-height:470px;overflow:auto;}#preview-content img,#preview-content video{max-width:100%;max-height:470px;display:block;border-radius:4px;}#preview-content audio{width:100%;margin-top:4px;}#preview-content .audio-meta{margin-top:4px;color:#bbb;font-size:11px;font-family:monospace;}</style>
<div id="preview"><div class="pv-header"><span class="title" id="pv-title">预览</span><button id="pv-pin" title="固定/取消固定">📌</button><button id="pv-close" title="关闭">✕</button></div><div id="preview-content"></div></div>
<script>(function(){const pv=document.getElementById('preview');const pvc=document.getElementById('preview-content');const titleEl=document.getElementById('pv-title');const pinBtn=document.getElementById('pv-pin');const closeBtn=document.getElementById('pv-close');let activeLink=null;let hideTimer=null;let pinned=false;let dragState=null;let currentType='';function esc(s){return s.replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;','\'':'&#39;'}[c]));}function build(href,text){let label=text||'';label=label.replace(/^[\[]|[\]]$/g,'');currentType='text';if(/\/image\//.test(href)){currentType='image';return '<img src="'+href+'" loading="lazy" />';}if(/\/video\//.test(href)){currentType='video';return '<video src="'+href+'" controls preload="metadata"></video>'; }if(/\/voice\//.test(href)){currentType='audio';return '<div class="audio-box"><audio src="'+href+'" controls preload="metadata"></audio><div class="audio-meta">解析中...</div></div>'; }if(/表情/.test(label)||/\.(gif|apng|webp)(\?|$)/i.test(href)){currentType='emoji';return '<img src="'+href+'" style="max-width:100%;max-height:470px;display:block;" />';}if(/\/file\//.test(href)){currentType='file';return '<div style="word-break:break-all;line-height:1.5;">文件: '+esc(label)+'<br/><a href="'+href+'" target="_blank" style="color:#61afef;">下载</a></div>'; }return '<div style="word-break:break-all;line-height:1.5;">'+esc(label)+'<br/><a href="'+href+'" target="_blank" style="color:#61afef;">打开</a></div>'; }function fmtDur(d){if(!isFinite(d)||d<=0)return '未知';const s=Math.round(d);if(s>=60){const m=Math.floor(s/60);const ss=s%60;return m+'m'+(ss<10?'0':'')+ss+'s';}return s+'s';}function parseLabelDuration(lbl){const m1=/语音\((\d+)s\)/.exec(lbl);if(m1)return m1[1]+'s';const m2=/语音\((\d+)m(\d{1,2})s\)/.exec(lbl);if(m2){const mm=m2[1],ss=m2[2];return mm+'m'+(ss.length===1?'0'+ss:ss)+'s';}return null;}function afterRender(){if(currentType==='audio'){const audio=pvc.querySelector('audio');const meta=pvc.querySelector('.audio-meta');if(audio&&meta){const label=(activeLink?activeLink.textContent:'').replace(/[\[\]]/g,'');const parsed=parseLabelDuration(label);if(parsed){meta.textContent='时长: '+parsed;}const update=()=>{if(isFinite(audio.duration)&&audio.duration>0){meta.textContent='时长: '+fmtDur(audio.duration);return true;}return false;};audio.addEventListener('loadedmetadata',()=>{update();},{once:true});let tries=0;const timer=setInterval(()=>{if(update()||++tries>6){clearInterval(timer);} },500);audio.load();}}}function adjustWidth(){if(dragState)return;const vw=window.innerWidth;const clamp=w=>Math.min(w,vw-40);switch(currentType){case'audio':pv.style.width=clamp(680)+'px';break;case'video':pv.style.width=clamp(720)+'px';break;case'file':pv.style.width=clamp(560)+'px';break;case'image':case'emoji':pv.style.width='auto';break;default:pv.style.width='420px';}}function showFor(a){clearTimeout(hideTimer);activeLink=a;const href=a.getAttribute('href');pvc.innerHTML=build(href,a.textContent||'');titleEl.textContent=a.textContent||'预览';pv.style.display='block';adjustWidth();afterRender();positionNear(a);}function positionNear(a){if(pinned||dragState)return;const rect=a.getBoundingClientRect();const pw=pv.offsetWidth;const ph=pv.offsetHeight;let x=rect.right+12;let y=rect.top;const vw=window.innerWidth;const vh=window.innerHeight;if(x+pw>vw-8)x=rect.left-pw-12;if(x<8)x=8;if(y+ph>vh-8)y=vh-ph-8;if(y<8)y=8;pv.style.left=x+'px';pv.style.top=y+'px';}function scheduleHide(){if(pinned)return;hideTimer=setTimeout(()=>{if(pinned)return;activeLink=null;pv.style.display='none';pvc.innerHTML='';},280);}document.addEventListener('mouseover',e=>{const a=e.target.closest('a.media');if(!a)return;if(a===activeLink){clearTimeout(hideTimer);return;}showFor(a);});document.addEventListener('mousemove',e=>{if(!activeLink||pinned||dragState)return;positionNear(activeLink);});pv.addEventListener('mouseenter',()=>{clearTimeout(hideTimer);});pv.addEventListener('mouseleave',()=>{scheduleHide();});document.addEventListener('mouseout',e=>{const a=e.target.closest&&e.target.closest('a.media');if(!a)return;if(pv.contains(e.relatedTarget))return;scheduleHide();});pinBtn.addEventListener('click',()=>{pinned=!pinned;pinBtn.style.opacity=pinned?1:0.6;if(!pinned){scheduleHide();}else{clearTimeout(hideTimer);}});closeBtn.addEventListener('click',()=>{pinned=false;activeLink=null;pv.style.display='none';pvc.innerHTML='';});pv.querySelector('.pv-header').addEventListener('mousedown',e=>{if(e.target===pinBtn||e.target===closeBtn)return;pinned=true;pinBtn.style.opacity=1;dragState={ox:e.clientX,oy:e.clientY,left:pv.offsetLeft,top:pv.offsetTop};pv.classList.add('dragging');e.preventDefault();});window.addEventListener('mousemove',e=>{if(!dragState)return;const dx=e.clientX-dragState.ox;const dy=e.clientY-dragState.oy;let nl=dragState.left+dx;let nt=dragState.top+dy;const vw=window.innerWidth;const vh=window.innerHeight;nl=Math.max(0,Math.min(vw-pv.offsetWidth,nl));nt=Math.max(0,Math.min(vh-pv.offsetHeight,nt));pv.style.left=nl+'px';pv.style.top=nt+'px';});window.addEventListener('mouseup',()=>{if(dragState){dragState=null;pv.classList.remove('dragging');}});window.addEventListener('keydown',e=>{if(e.key==='Escape'){pinned=false;pv.style.display='none';pvc.innerHTML='';activeLink=null;}});})();</script>`

var previewVoiceSnippet = `
<style>
.voice-entry{display:inline-flex;align-items:center;gap:6px;margin:4px 0;flex-wrap:wrap;}
.voice-transcribe-btn{padding:2px 8px;font-size:12px;border:1px solid #888;background:#f0f0f0;color:#222;border-radius:6px;cursor:pointer;transition:opacity .2s ease;}
.voice-transcribe-btn--busy,
.voice-transcribe-btn:disabled{opacity:0.6;cursor:wait;}
.voice-transcribe-result{font-size:12px;color:#444;min-height:1em;max-width:520px;white-space:pre-wrap;word-break:break-word;}
</style>
<script>
(function(){
	if(window.__chatlogVoiceHandler){return;}
	window.__chatlogVoiceHandler = true;

	document.addEventListener('click', async function(ev){
		const btn = ev.target.closest('.voice-transcribe-btn');
		if(!btn){return;}
		ev.preventDefault();

		const container = btn.closest('.voice-entry');
		const link = container ? container.querySelector('a.voice-link') : null;
		const result = container ? container.querySelector('.voice-transcribe-result') : null;
		if(!link){return;}

		const href = link.getAttribute('href');
		if(!href){return;}

		let url;
		try{
			url = new URL(href, window.location.origin);
		}catch(err){
			if(result){
				result.textContent = '链接无效';
				result.dataset.status = 'error';
			}
			return;
		}

		url.searchParams.set('transcribe', '1');

		const previous = result ? result.textContent : '';
		if(result){
			result.textContent = '转写中...';
			result.dataset.status = 'loading';
		}

		btn.disabled = true;
		btn.classList.add('voice-transcribe-btn--busy');

		try{
			const resp = await fetch(url.toString(), { headers: { 'Accept': 'application/json' } });
			if(!resp.ok){
				throw new Error('HTTP ' + resp.status);
			}

			let data = null;
			const ct = resp.headers.get('content-type') || '';
			if(ct.indexOf('application/json') >= 0){
				data = await resp.json();
			}

			const text = data && typeof data.text === 'string' ? data.text.trim() : '';
			if(result){
				if(text){
					result.textContent = text;
					result.dataset.status = 'done';
				}else{
					result.textContent = '未识别到语音内容';
					result.dataset.status = 'empty';
				}
				if(data && data.language){ result.dataset.language = data.language; }
				if(data && data.duration !== undefined){ result.dataset.duration = String(data.duration); }
			}
		}catch(err){
			if(result){
				result.textContent = '转写失败';
				result.dataset.status = 'error';
			}
			console.error('voice transcription failed', err);
		}finally{
			btn.disabled = false;
			btn.classList.remove('voice-transcribe-btn--busy');
			if(result && result.dataset.status === 'loading'){
				result.textContent = previous;
				result.dataset.status = '';
			}
		}
	});
})();
</script>`

var previewHTMLSnippet = previewHTMLSnippetBase + previewVoiceSnippet

var chatlogHTMLHeadTemplate = `<html><head><meta charset="utf-8"><title>%s</title><style>
body{font-family:Arial,Helvetica,sans-serif;font-size:14px;line-height:1.4;background:#f8f9fb;padding:24px;color:#2c3e50;}
h1{margin:0 0 16px;font-size:22px;}
h2{margin:24px 0 12px;font-size:18px;}
p.meta{margin:4px 0;color:#5f6c7b;}
.search-meta{background:#fff;padding:18px;border-radius:10px;box-shadow:0 1px 4px rgba(18,38,63,0.08);margin-bottom:18px;}
details{margin:8px 0;padding:6px 10px;border:1px solid #dde1eb;border-radius:8px;background:#fff;box-shadow:0 1px 3px rgba(18,38,63,0.06);}
summary{cursor:pointer;font-weight:600;color:#2c3e50;}
.msg{margin:12px 0;padding:12px 14px;border-left:3px solid #3498db;background:#fff;border-radius:10px;box-shadow:0 1px 3px rgba(18,38,63,0.08);}
.msg-row{display:flex;gap:12px;align-items:flex-start;}
.avatar{width:36px;height:36px;border-radius:9px;object-fit:cover;background:#f2f2f2;border:1px solid #eee;flex:0 0 36px;}
.msg-content{flex:1;min-width:0;}
.meta{color:#5f6c7b;font-size:12px;display:flex;flex-wrap:wrap;gap:12px;margin-bottom:6px;align-items:center;}
.meta .talker{color:#2c3e50;font-weight:600;}
.meta .sender{color:#2c3e50;}
.meta .time{color:#16a085;}
.meta .score{font-family:monospace;color:#a0aec0;}
pre{white-space:pre-wrap;word-break:break-word;margin:6px 0 0;}
.empty{padding:28px;text-align:center;color:#768390;background:#fff;border-radius:10px;box-shadow:0 1px 4px rgba(18,38,63,0.08);}
a.media{color:#2c3e50;text-decoration:none;border-bottom:1px dashed rgba(44,62,80,0.45);}
a.media:hover{color:#0f4c81;}
</style></head><body>`

func writeChatlogHTMLHeader(w io.Writer, title string) {
	fmt.Fprintf(w, chatlogHTMLHeadTemplate, template.HTMLEscapeString(title))
}

func (s *Service) initRouter() {
	s.initBaseRouter()
	s.initMediaRouter()
	s.initAPIRouter()
	s.initMCPRouter()
}

func (s *Service) initBaseRouter() {
	staticDir, _ := fs.Sub(EFS, "static")
	s.router.StaticFS("/static", http.FS(staticDir))
	s.router.StaticFileFS("/favicon.ico", "./favicon.ico", http.FS(staticDir))
	s.router.StaticFileFS("/", "./index.htm", http.FS(staticDir))
	s.router.GET("/health", func(ctx *gin.Context) { ctx.JSON(http.StatusOK, gin.H{"status": "ok"}) })
	s.router.NoRoute(func(c *gin.Context) {
		path := c.Request.URL.Path
		if strings.HasPrefix(path, "/api") || strings.HasPrefix(path, "/static") {
			c.JSON(http.StatusNotFound, gin.H{"error": "Not found"})
			return
		}
		c.Header("Cache-Control", "no-cache, no-store, max-age=0, must-revalidate, value")
		c.Redirect(http.StatusFound, "/")
	})
}

func (s *Service) initMediaRouter() {
	s.router.GET("/image/*key", func(c *gin.Context) { s.handleMedia(c, "image") })
	s.router.GET("/video/*key", func(c *gin.Context) { s.handleMedia(c, "video") })
	s.router.GET("/file/*key", func(c *gin.Context) { s.handleMedia(c, "file") })
	s.router.GET("/voice/*key", func(c *gin.Context) { s.handleMedia(c, "voice") })
	s.router.GET("/data/*path", s.handleMediaData)
	s.router.GET("/avatar/:username", s.handleAvatar)
}

func (s *Service) initAPIRouter() {
	api := s.router.Group("/api/v1")
	{
		api.GET("/setting", s.handleGetSetting)
		api.POST("/setting", s.handleUpdateSetting)

		actions := api.Group("/actions")
		actions.POST("/get-data-key", s.handleActionGetDataKey)
		actions.POST("/decrypt", s.handleActionDecrypt)
		actions.POST("/http/start", s.handleActionStartHTTP)
		actions.POST("/http/stop", s.handleActionStopHTTP)
		actions.POST("/auto-decrypt/start", s.handleActionStartAutoDecrypt)
		actions.POST("/auto-decrypt/stop", s.handleActionStopAutoDecrypt)

		dataAPI := api.Group("", s.checkDBStateMiddleware())
		dataAPI.GET("/chatlog", s.handleChatlog)
		dataAPI.GET("/contact", s.handleContacts)
		dataAPI.GET("/chatroom", s.handleChatRooms)
		dataAPI.GET("/session", s.handleSessions)
		dataAPI.GET("/diary", s.handleDiary)
		dataAPI.GET("/dashboard", s.handleDashboard)
		dataAPI.GET("/search", s.handleSearch)
	}
}

func (s *Service) initMCPRouter() {
	s.router.Any("/mcp", func(c *gin.Context) { s.mcpStreamableServer.ServeHTTP(c.Writer, c.Request) })
	s.router.Any("/sse", func(c *gin.Context) { s.mcpSSEServer.ServeHTTP(c.Writer, c.Request) })
	s.router.Any("/message", func(c *gin.Context) { s.mcpSSEServer.ServeHTTP(c.Writer, c.Request) })
}

// GET /api/v1/dashboard
func (s *Service) handleDashboard(c *gin.Context) {
	// 基础聚合
	gstats, err := s.db.GetDB().GlobalMessageStats()
	if err != nil {
		c.JSON(http.StatusInternalServerError, gin.H{"error": "global stats failed", "detail": err.Error()})
		return
	}
	groupCounts, _ := s.db.GetDB().GroupMessageCounts()

	// 文件与目录大小
	dataDir := s.conf.GetDataDir()
	workDir := dataDir
	if s.db != nil {
		if wd := s.db.GetWorkDir(); wd != "" {
			workDir = wd
		}
	}
	dirSize := safeDirSize(dataDir)
	dbSize := estimateDBSize(workDir)

	// 当前账号昵称（overview.user）：优先从 WorkDir/DataDir 路径中提取 wxid_***，再用联系人 NickName 映射；找不到则回退 wxid
	extractWxid := func(p string) string {
		p = strings.TrimSpace(p)
		if p == "" {
			return ""
		}
		// 遍历路径片段，优先返回形如 wxid_ 开头的片段
		parts := strings.Split(filepath.Clean(p), string(filepath.Separator))
		for _, seg := range parts {
			if strings.HasPrefix(strings.ToLower(seg), "wxid_") {
				return seg
			}
		}
		// 兜底返回最后一段
		return filepath.Base(filepath.Clean(p))
	}

	currentUser := ""
	accountID := ""
	// 先从 WorkDir 提取（更贴近实际解密目录结构），再从 DataDir 提取
	if wd := s.db.GetWorkDir(); wd != "" && accountID == "" {
		accountID = extractWxid(wd)
	}
	if accountID == "" {
		accountID = extractWxid(dataDir)
	}

	// 若拿到候选 accountID，则尝试用联系人映射 NickName
	if accountID != "" && accountID != "." && accountID != string(filepath.Separator) {
		// Windows WeChat 4.x: v3 对应 wxid 可能带有第二段后缀，如 wxid_xxx_yyyy
		// 查找昵称时需要去掉第二个下划线及其后内容
		lookupID := accountID
		low := strings.ToLower(lookupID)
		if strings.HasPrefix(low, "wxid_") {
			// 定位第二个下划线位置
			rest := lookupID[len("wxid_"):]
			if idx := strings.Index(rest, "_"); idx >= 0 {
				lookupID = lookupID[:len("wxid_")+idx]
			}
		}
		if clist, err := s.db.GetContacts(lookupID, 0, 0); err == nil && clist != nil {
			for _, it := range clist.Items {
				if it != nil && it.UserName == lookupID {
					if strings.TrimSpace(it.NickName) != "" {
						currentUser = it.NickName
					}
					break
				}
			}
			if currentUser == "" && len(clist.Items) > 0 && clist.Items[0] != nil && clist.Items[0].UserName == lookupID {
				currentUser = clist.Items[0].NickName
			}
		}
		// 最终兜底：回退为 wxid/accountID
		if strings.TrimSpace(currentUser) == "" {
			currentUser = accountID
		}
	}

	// 使用结构体固定 JSON 输出顺序
	type DBStats struct {
		DbSizeMB  float64 `json:"db_size_mb"`
		DirSizeMB float64 `json:"dir_size_mb"`
	}
	type MsgStats struct {
		TotalMsgs      int64 `json:"total_msgs"`
		SentMsgs       int64 `json:"sent_msgs"`
		ReceivedMsgs   int64 `json:"received_msgs"`
		UniqueMsgTypes int   `json:"unique_msg_types"`
	}
	type OverviewGroup struct {
		ChatRoomName string `json:"ChatRoomName"`
		NickName     string `json:"NickName"`
		MemberCount  int    `json:"member_count"`
		MessageCount int64  `json:"message_count"`
	}
	type Timeline struct {
		Earliest int64 `json:"earliest_msg_time"`
		Latest   int64 `json:"latest_msg_time"`
		Duration int   `json:"duration_days"`
	}
	type Migration struct {
		ID        int    `json:"id"`
		File      string `json:"file"`
		Status    string `json:"status"`
		CreatedAt string `json:"created_at"`
	}
	type Overview struct {
		User       string           `json:"user"`
		DBStats    DBStats          `json:"dbStats"`
		MsgStats   MsgStats         `json:"msgStats"`
		MsgTypes   map[string]int64 `json:"msgTypes"`
		Groups     []OverviewGroup  `json:"groups"`
		Timeline   Timeline         `json:"timeline"`
		Migrations []Migration      `json:"migrations"`
	}

	type GroupOverview struct {
		TotalGroups    int    `json:"total_groups"`
		ActiveGroups   int    `json:"active_groups"`
		TodayMessages  int    `json:"today_messages"`
		WeeklyAvg      int    `json:"weekly_avg"`
		MostActiveHour string `json:"most_active_hour"`
	}
	type ContentAnalysis struct {
		Text   int64 `json:"text_messages"`
		Images int64 `json:"images"`
		Voice  int64 `json:"voice_messages"`
		Files  int64 `json:"files"`
		Links  int64 `json:"links"`
		Others int64 `json:"others"`
	}
	type GroupListItem struct {
		Name     string `json:"name"`
		Members  int    `json:"members"`
		Messages int64  `json:"messages"`
		Active   bool   `json:"active"`
	}
	type GroupAnalysis struct {
		Title           string          `json:"title"`
		Overview        GroupOverview   `json:"overview"`
		ContentAnalysis ContentAnalysis `json:"content_analysis"`
		GroupList       []GroupListItem `json:"group_list"`
	}
	type ContentTypeStats struct {
		Count      int64    `json:"count"`
		Percentage float64  `json:"percentage"`
		SizeMB     *float64 `json:"size_mb,omitempty"`
		Trend      *string  `json:"trend,omitempty"`
	}
	type SourceChannel struct {
		Count      int64   `json:"count"`
		Percentage float64 `json:"percentage"`
	}
	type ProcessingStatus struct {
		Processed  int `json:"processed"`
		Processing int `json:"processing"`
		Pending    int `json:"pending"`
	}
	type QualityMetrics struct {
		DataIntegrity          float64 `json:"data_integrity"`
		ClassificationAccuracy float64 `json:"classification_accuracy"`
		DuplicateRate          float64 `json:"duplicate_rate"`
		ErrorRate              float64 `json:"error_rate"`
	}
	type DataTypeAnalysis struct {
		Title            string                      `json:"title"`
		ContentTypes     map[string]ContentTypeStats `json:"content_types"`
		SourceChannels   map[string]SourceChannel    `json:"source_channels"`
		ProcessingStatus ProcessingStatus            `json:"processing_status"`
		QualityMetrics   QualityMetrics              `json:"quality_metrics"`
		PieGradient      string                      `json:"pieGradient,omitempty"`
	}
	type VisualizationDefaults struct {
		SelectedGroupIndex int `json:"selectedGroupIndex"`
	}
	type RelationshipNode struct {
		Name     string `json:"name"`
		Type     string `json:"type"`
		Messages int64  `json:"messages"`
		Avatar   string `json:"avatar,omitempty"`
	}
	type RelationshipNetwork struct {
		Nodes []RelationshipNode `json:"nodes"`
	}
	type Visualization struct {
		Defaults            VisualizationDefaults `json:"defaults"`
		GroupAnalysis       GroupAnalysis         `json:"groupAnalysis"`
		DataTypeAnalysis    DataTypeAnalysis      `json:"dataTypeAnalysis"`
		RelationshipNetwork RelationshipNetwork   `json:"relationshipNetwork"`
	}
	type Dashboard struct {
		Overview      Overview      `json:"overview"`
		Visualization Visualization `json:"visualization"`
	}

	// 群信息（合并消息计数）
	type groupAggregate struct {
		id       string
		nickName string
		members  int
		messages int64
		active   bool
	}
	groupAggs := make([]groupAggregate, 0)
	activeGroups := 0
	if rooms, err := s.db.GetChatRooms("", 0, 0); err == nil {
		for _, r := range rooms.Items {
			if strings.TrimSpace(r.NickName) == "" {
				continue
			}
			mc := groupCounts[r.Name]
			active := mc > 0
			if active {
				activeGroups++
			}
			groupAggs = append(groupAggs, groupAggregate{
				id:       r.Name,
				nickName: r.NickName,
				members:  len(r.Users),
				messages: mc,
				active:   active,
			})
		}
	}
	sort.Slice(groupAggs, func(i, j int) bool {
		if groupAggs[i].messages == groupAggs[j].messages {
			return groupAggs[i].nickName < groupAggs[j].nickName
		}
		return groupAggs[i].messages > groupAggs[j].messages
	})
	overviewGroups := make([]OverviewGroup, 0, len(groupAggs))
	groupList := make([]GroupListItem, 0, len(groupAggs))
	for _, g := range groupAggs {
		overviewGroups = append(overviewGroups, OverviewGroup{
			ChatRoomName: g.id,
			NickName:     g.nickName,
			MemberCount:  g.members,
			MessageCount: g.messages,
		})
		groupList = append(groupList, GroupListItem{
			Name:     g.nickName,
			Members:  g.members,
			Messages: g.messages,
			Active:   g.active,
		})
	}
	totalGroups := len(groupAggs)

	// msgTypes 依据最新文档 + 衍生细分（文件消息 / 链接消息）补齐
	msgTypes := map[string]int64{
		"文本消息":    0,
		"图片消息":    0,
		"语音消息":    0,
		"好友验证消息":  0,
		"好友推荐消息":  0,
		"聊天表情":    0,
		"位置消息":    0,
		"XML消息":   0, // 未细分的 49 类或其他 XML
		"文件消息":    0,
		"链接消息":    0,
		"音视频通话":   0,
		"手机端操作消息": 0,
		"系统通知":    0,
		"撤回消息":    0,
	}
	for k, v := range gstats.ByType {
		if _, ok := msgTypes[k]; ok {
			msgTypes[k] += v
		}
	}

	// 时间轴
	durationDays := 0
	if gstats.EarliestUnix > 0 && gstats.LatestUnix >= gstats.EarliestUnix {
		span := gstats.LatestUnix - gstats.EarliestUnix
		if span < 0 {
			span = 0
		}
		durationDays = int(math.Round(float64(span) / 86400.0))
	}

	uniqueTypes := 0
	for _, v := range msgTypes {
		if v > 0 {
			uniqueTypes++
		}
	}

	// 今日每小时统计用于 most_active_hour
	perHourTotal := make([]int64, 24)
	if s.db != nil && s.db.GetDB() != nil {
		if hours, err := s.db.GetDB().GlobalTodayHourly(); err == nil {
			for i := 0; i < 24; i++ {
				perHourTotal[i] = hours[i]
			}
		}
	}
	maxHour := 0
	for h := 1; h < 24; h++ {
		if perHourTotal[h] > perHourTotal[maxHour] {
			maxHour = h
		}
	}
	mostActiveHour := fmt.Sprintf("%02d:00-%02d:00", maxHour, (maxHour+1)%24)

	// 内容占比（基于 msgTypes）
	totalMsgs := gstats.Total
	pct := func(n int64) float64 {
		if totalMsgs == 0 {
			return 0
		}
		return math.Round((float64(n) * 10000.0 / float64(totalMsgs))) / 100.0
	}
	// 私聊/群聊分布（用于 DataTypeAnalysis.SourceChannels）
	var groupTotal int64
	for _, v := range groupCounts {
		groupTotal += v
	}
	privateTotal := totalMsgs - groupTotal

	// ====== 今日群聊消息数统计 ======
	todayMessages := int64(0)
	if s.db != nil && s.db.GetDB() != nil {
		if todayCounts, err := s.db.GetDB().GroupTodayMessageCounts(); err == nil {
			for _, v := range todayCounts {
				todayMessages += v
			}
		}
	}

	// ====== 本周群聊平均每天消息数 ======
	weeklyAvg := 0
	if s.db != nil && s.db.GetDB() != nil {
		if weekTotal, err := s.db.GetDB().GroupWeekMessageCount(); err == nil && weekTotal > 0 {
			// 计算已过天数：周一=1, 周二=2 ... 周六=6, 周日=7（显示完整7天平均）
			now := time.Now()
			wday := int(now.Weekday()) // Sunday=0
			passed := 0
			if wday == 0 { // Sunday
				passed = 7
			} else {
				passed = wday
			}
			if passed <= 0 {
				passed = 1
			}
			avg := float64(weekTotal) / float64(passed)
			weeklyAvg = int(math.Round(avg))
		}
	}

	// ===== 归一化 content_types 百分比（合计 100%）=====
	// 参与归一化的类别列表（与 DataTypeAnalysis.content_types 一致）
	ctKeys := []string{
		"XML消息", "位置消息", "图片消息", "好友推荐消息", "好友验证消息", "手机端操作消息",
		"撤回消息", "文件消息", "文本消息", "系统通知", "聊天表情", "语音消息", "链接消息", "音视频通话",
	}
	var sumCT int64
	maxKey := ""
	var maxCnt int64
	for _, k := range ctKeys {
		sumCT += msgTypes[k]
		if msgTypes[k] > maxCnt {
			maxCnt = msgTypes[k]
			maxKey = k
		}
	}
	round2 := func(f float64) float64 { return math.Round(f*100) / 100 }
	pctCT := func(n int64) float64 {
		if sumCT == 0 {
			return 0
		}
		return round2(float64(n) * 100.0 / float64(sumCT))
	}
	// 先计算每类百分比与总和
	ctPerc := make(map[string]float64, len(ctKeys))
	sumPerc := 0.0
	for _, k := range ctKeys {
		p := pctCT(msgTypes[k])
		ctPerc[k] = p
		sumPerc += p
	}
	// 差额校正到 100%
	if diff := round2(100.0 - sumPerc); diff != 0 && maxKey != "" {
		ctPerc[maxKey] = round2(ctPerc[maxKey] + diff)
	}

	// ===== 关系网络（亲密度）=====
	relationshipNodes := make([]RelationshipNode, 0)
	if s.db != nil && s.db.GetDB() != nil {
		if ibase, err := s.db.GetDB().IntimacyBase(); err == nil && len(ibase) > 0 {
			skipIDs := map[string]struct{}{
				"filehelper":    {},
				"weixin":        {},
				"notifymessage": {},
				"fmessage":      {},
			}
			contactMap := map[string]*model.Contact{}
			if clist, err := s.db.GetContacts("", 0, 0); err == nil && clist != nil {
				for _, ct := range clist.Items {
					if ct != nil {
						contactMap[ct.UserName] = ct
					}
				}
			}
			type pair struct {
				k string
				v *model.IntimacyBase
			}
			arr := make([]pair, 0, len(ibase))
			for k, v := range ibase {
				arr = append(arr, pair{k, v})
			}
			sort.Slice(arr, func(i, j int) bool {
				ai, aj := arr[i].v, arr[j].v
				if ai.Last90DaysMsg != aj.Last90DaysMsg {
					return ai.Last90DaysMsg > aj.Last90DaysMsg
				}
				if ai.MsgCount != aj.MsgCount {
					return ai.MsgCount > aj.MsgCount
				}
				return ai.Past7DaysSentMsg > aj.Past7DaysSentMsg
			})
			maxN := 24
			if len(arr) < maxN {
				maxN = len(arr)
			}
			added := 0
			for idx := 0; idx < len(arr) && added < maxN; idx++ {
				k := arr[idx].k
				v := arr[idx].v
				if accountID != "" && k == accountID {
					continue
				}
				if _, skip := skipIDs[k]; skip {
					continue
				}
				ct := contactMap[k]
				display := k
				if ct != nil {
					if strings.TrimSpace(ct.Remark) != "" {
						display = ct.Remark
					} else if strings.TrimSpace(ct.NickName) != "" {
						display = ct.NickName
					}
				}
				relationshipNodes = append(relationshipNodes, RelationshipNode{
					Name:     display,
					Type:     "contact",
					Messages: v.MsgCount,
					Avatar:   s.composeAvatarURL(k),
				})
				added++
			}
		}
	}

	others := totalMsgs - (msgTypes["文本消息"] + msgTypes["图片消息"] + msgTypes["语音消息"] + msgTypes["文件消息"] + msgTypes["链接消息"])
	if others < 0 {
		others = 0
	}
	defaultSelectedIndex := 0
	if len(groupList) == 0 {
		defaultSelectedIndex = -1
	}
	processingStatus := ProcessingStatus{}
	if totalMsgs > 0 {
		processingStatus.Processed = 100
	}
	qualityMetrics := QualityMetrics{}
	floatPtr := func(v float64) *float64 { return &v }
	stringPtr := func(v string) *string { return &v }
	vis := Visualization{
		Defaults: VisualizationDefaults{SelectedGroupIndex: defaultSelectedIndex},
		GroupAnalysis: GroupAnalysis{
			Title: "群聊分析",
			Overview: GroupOverview{
				TotalGroups:    totalGroups,
				ActiveGroups:   activeGroups,
				TodayMessages:  int(todayMessages),
				WeeklyAvg:      weeklyAvg,
				MostActiveHour: mostActiveHour,
			},
			ContentAnalysis: ContentAnalysis{
				Text:   msgTypes["文本消息"],
				Images: msgTypes["图片消息"],
				Voice:  msgTypes["语音消息"],
				Files:  msgTypes["文件消息"],
				Links:  msgTypes["链接消息"],
				Others: others,
			},
			GroupList: groupList,
		},
		DataTypeAnalysis: DataTypeAnalysis{
			Title: "数据类型统计",
			ContentTypes: map[string]ContentTypeStats{
				"文本消息":    {Count: msgTypes["文本消息"], Percentage: ctPerc["文本消息"]},
				"图片消息":    {Count: msgTypes["图片消息"], Percentage: ctPerc["图片消息"]},
				"语音消息":    {Count: msgTypes["语音消息"], Percentage: ctPerc["语音消息"]},
				"文件消息":    {Count: msgTypes["文件消息"], Percentage: ctPerc["文件消息"]},
				"链接消息":    {Count: msgTypes["链接消息"], Percentage: ctPerc["链接消息"], SizeMB: floatPtr(0), Trend: stringPtr("")},
				"XML消息":   {Count: msgTypes["XML消息"], Percentage: ctPerc["XML消息"]},
				"好友验证消息":  {Count: msgTypes["好友验证消息"], Percentage: ctPerc["好友验证消息"]},
				"好友推荐消息":  {Count: msgTypes["好友推荐消息"], Percentage: ctPerc["好友推荐消息"]},
				"聊天表情":    {Count: msgTypes["聊天表情"], Percentage: ctPerc["聊天表情"]},
				"位置消息":    {Count: msgTypes["位置消息"], Percentage: ctPerc["位置消息"]},
				"音视频通话":   {Count: msgTypes["音视频通话"], Percentage: ctPerc["音视频通话"]},
				"手机端操作消息": {Count: msgTypes["手机端操作消息"], Percentage: ctPerc["手机端操作消息"]},
				"系统通知":    {Count: msgTypes["系统通知"], Percentage: ctPerc["系统通知"]},
				"撤回消息":    {Count: msgTypes["撤回消息"], Percentage: ctPerc["撤回消息"]},
			},
			SourceChannels: map[string]SourceChannel{
				"私聊数据": {Count: privateTotal, Percentage: pct(privateTotal)},
				"群聊数据": {Count: groupTotal, Percentage: pct(groupTotal)},
			},
			ProcessingStatus: processingStatus,
			QualityMetrics:   qualityMetrics,
			PieGradient:      "#3b82f6 0deg 180deg, #10b981 180deg 270deg, #f59e0b 270deg 315deg, #ef4444 315deg 360deg",
		},
		RelationshipNetwork: RelationshipNetwork{Nodes: relationshipNodes},
	}

	resp := Dashboard{
		Overview: Overview{
			User:       currentUser,
			DBStats:    DBStats{DbSizeMB: roundMB(dbSize), DirSizeMB: roundMB(dirSize)},
			MsgStats:   MsgStats{TotalMsgs: gstats.Total, SentMsgs: gstats.Sent, ReceivedMsgs: gstats.Received, UniqueMsgTypes: uniqueTypes},
			MsgTypes:   msgTypes,
			Groups:     overviewGroups,
			Timeline:   Timeline{Earliest: gstats.EarliestUnix, Latest: gstats.LatestUnix, Duration: durationDays},
			Migrations: []Migration{},
		},
		Visualization: vis,
	}

	// ===== 持久化 dashboard （单一文件）=====
	// 仅保存一个固定文件：<WorkDir|DataDir>/dashboard.json
	baseDir := ""
	if s.db != nil {
		if wd := strings.TrimSpace(s.db.GetWorkDir()); wd != "" {
			baseDir = wd
		}
	}
	if baseDir == "" {
		if dir := strings.TrimSpace(s.conf.GetDataDir()); dir != "" {
			baseDir = dir
		}
	}
	if baseDir == "" {
		if cwd, err := os.Getwd(); err == nil {
			baseDir = cwd
		}
	}
	if baseDir != "" {
		if err := os.MkdirAll(baseDir, 0o755); err == nil {
			if b, err := json.Marshal(resp); err == nil {
				path := filepath.Join(baseDir, "dashboard.json")
				_ = os.WriteFile(path, b, 0o644)
			}
		}
	}

	if c.Query("download") == "1" {
		b, err := json.MarshalIndent(resp, "", "  ")
		if err != nil {
			c.JSON(http.StatusInternalServerError, gin.H{"error": "marshal failed", "detail": err.Error()})
			return
		}
		c.Header("Content-Type", "application/json")
		c.Header("Content-Disposition", "attachment; filename=dashboard.json")
		c.Data(http.StatusOK, "application/json", b)
		return
	}
	c.JSON(http.StatusOK, resp)
}

func roundMB(bytes int64) float64 {
	if bytes <= 0 {
		return 0
	}
	// 1 MB = 1024*1024
	mb := float64(bytes) / (1024.0 * 1024.0)
	// round to 2 decimals
	return float64(int(mb*100+0.5)) / 100.0
}

// safeDirSize walks a directory and sums file sizes; returns 0 on error.
func safeDirSize(path string) int64 {
	var total int64
	if path == "" {
		return 0
	}
	_ = filepath.Walk(path, func(p string, info os.FileInfo, err error) error {
		if err != nil {
			return nil
		}
		if info == nil || info.IsDir() {
			return nil
		}
		total += info.Size()
		return nil
	})
	return total
}

// estimateDBSize sums sizes of common DB files under workDir
func estimateDBSize(workDir string) int64 {
	if workDir == "" {
		return 0
	}
	var total int64
	_ = filepath.Walk(workDir, func(p string, info os.FileInfo, err error) error {
		if err != nil || info == nil || info.IsDir() {
			return nil
		}
		name := strings.ToLower(info.Name())
		if strings.HasSuffix(name, ".db") || strings.HasSuffix(name, ".sqlite") || strings.HasSuffix(name, ".sqlite3") || strings.HasSuffix(name, ".db-wal") || strings.HasSuffix(name, ".db-shm") {
			total += info.Size()
		}
		return nil
	})
	return total
}

func (s *Service) handleSearch(c *gin.Context) {
	params := struct {
		Query  string `form:"q"`
		Talker string `form:"talker"`
		Sender string `form:"sender"`
		Time   string `form:"time"`
		Start  string `form:"start"`
		End    string `form:"end"`
		Limit  int    `form:"limit"`
		Offset int    `form:"offset"`
		Format string `form:"format"`
	}{}

	if err := c.BindQuery(&params); err != nil {
		errors.Err(c, err)
		return
	}

	query := strings.TrimSpace(params.Query)

	talker := strings.TrimSpace(params.Talker)

	limit := params.Limit
	if limit <= 0 {
		limit = 20
	}
	if limit > 200 {
		limit = 200
	}
	offset := params.Offset
	if offset < 0 {
		offset = 0
	}

	req := &model.SearchRequest{
		Query:  query,
		Talker: talker,
		Sender: strings.TrimSpace(params.Sender),
		Limit:  limit,
		Offset: offset,
	}

	if params.Time != "" {
		start, end, ok := util.TimeRangeOf(params.Time)
		if !ok {
			errors.Err(c, errors.InvalidArg("time"))
			return
		}
		req.Start = start
		req.End = end
	} else {
		if params.Start != "" && params.End != "" {
			start, end, ok := util.TimeRangeOf(params.Start + "~" + params.End)
			if !ok {
				errors.Err(c, errors.InvalidArg("time"))
				return
			}
			req.Start = start
			req.End = end
		} else if params.Start != "" {
			start, end, ok := util.TimeRangeOf(params.Start)
			if !ok {
				errors.Err(c, errors.InvalidArg("start"))
				return
			}
			req.Start = start
			req.End = end
		} else if params.End != "" {
			start, end, ok := util.TimeRangeOf(params.End)
			if !ok {
				errors.Err(c, errors.InvalidArg("end"))
				return
			}
			req.Start = start
			req.End = end
		}
	}

	if !req.Start.IsZero() && !req.End.IsZero() && req.End.Before(req.Start) {
		req.Start, req.End = req.End, req.Start
	}

	resp, err := s.db.SearchMessages(req)
	if err != nil {
		errors.Err(c, err)
		return
	}
	if resp == nil {
		resp = &model.SearchResponse{Hits: []*model.SearchHit{}, Limit: limit, Offset: offset}
	}

	resp.Query = req.Query
	resp.Talker = req.Talker
	resp.Sender = req.Sender
	resp.Start = req.Start
	resp.End = req.End
	resp.Limit = limit
	resp.Offset = offset

	format := strings.ToLower(strings.TrimSpace(params.Format))
	if format == "" {
		format = "json"
	}

	switch format {
	case "html":
		c.Writer.Header().Set("Content-Type", "text/html; charset=utf-8")
		writeChatlogHTMLHeader(c.Writer, "Search Result")
		c.Writer.WriteString("<h1>搜索结果</h1>")
		c.Writer.WriteString("<div class=\"search-meta\">")
		if resp.Query != "" {
			c.Writer.WriteString("<p class=\"meta\"><strong>关键词：</strong>" + template.HTMLEscapeString(resp.Query) + "</p>")
		}
		talkerLabel := "全部会话"
		if resp.Talker != "" {
			talkerLabel = template.HTMLEscapeString(resp.Talker)
		}
		c.Writer.WriteString("<p class=\"meta\"><strong>会话：</strong>" + talkerLabel + "</p>")
		if resp.Sender != "" {
			c.Writer.WriteString("<p class=\"meta\"><strong>发送者：</strong>" + template.HTMLEscapeString(resp.Sender) + "</p>")
		}
		timeLabel := "不限"
		if !resp.Start.IsZero() && !resp.End.IsZero() {
			timeLabel = resp.Start.Format("2006-01-02 15:04:05") + " ~ " + resp.End.Format("2006-01-02 15:04:05")
		} else if !resp.Start.IsZero() {
			timeLabel = ">= " + resp.Start.Format("2006-01-02 15:04:05")
		} else if !resp.End.IsZero() {
			timeLabel = "<= " + resp.End.Format("2006-01-02 15:04:05")
		}
		c.Writer.WriteString("<p class=\"meta\"><strong>时间范围：</strong>" + template.HTMLEscapeString(timeLabel) + "</p>")
		c.Writer.WriteString(fmt.Sprintf("<p class=\"meta\"><strong>命中条数：</strong>%d（本页 %d 条）</p>", resp.Total, len(resp.Hits)))
		c.Writer.WriteString("</div>")

		if len(resp.Hits) == 0 {
			c.Writer.WriteString("<div class=\"empty\">暂无搜索结果</div>")
		} else {
			for idx, hit := range resp.Hits {
				if hit == nil || hit.Message == nil {
					continue
				}
				msg := hit.Message
				msg.SetContent("host", c.Request.Host)
				talkerDisplay := msg.Talker
				if msg.TalkerName != "" {
					talkerDisplay = fmt.Sprintf("%s (%s)", msg.TalkerName, msg.Talker)
				}
				senderDisplay := msg.Sender
				if msg.IsSelf {
					senderDisplay = "我"
				}
				if msg.SenderName != "" {
					senderDisplay = fmt.Sprintf("%s(%s)", msg.SenderName, msg.Sender)
				}
				avatarURL := template.HTMLEscapeString(s.composeAvatarURL(msg.Sender) + "?size=big")
				talkerText := template.HTMLEscapeString(talkerDisplay)
				senderText := template.HTMLEscapeString(senderDisplay)
				timeText := template.HTMLEscapeString(msg.Time.Format("2006-01-02 15:04:05"))
				c.Writer.WriteString("<div class=\"msg\"><div class=\"msg-row\"><img class=\"avatar\" src=\"" + avatarURL + "\" loading=\"lazy\" alt=\"avatar\" onerror=\"this.style.visibility='hidden'\"/><div class=\"msg-content\">")
				c.Writer.WriteString("<div class=\"meta\"><span class=\"talker\">#" + fmt.Sprintf("%d", idx+1) + " · " + talkerText + "</span><span class=\"sender\">" + senderText + "</span><span class=\"time\">" + timeText + "</span>")
				if hit.Score > 0 {
					c.Writer.WriteString("<span class=\"score\">score: " + fmt.Sprintf("%.4f", hit.Score) + "</span>")
				}
				c.Writer.WriteString("</div>")
				c.Writer.WriteString("<pre>" + messageHTMLPlaceholder(msg) + "</pre>")
				c.Writer.WriteString("</div></div></div>")
			}
		}
		c.Writer.WriteString(previewHTMLSnippet)
		c.Writer.WriteString("</body></html>")
		return
	case "text", "plain":
		c.Writer.Header().Set("Content-Type", "text/plain; charset=utf-8")
		c.Writer.Header().Set("Cache-Control", "no-cache")
		c.Writer.Header().Set("Connection", "keep-alive")
		fmt.Fprintf(c.Writer, "关键词: %s\n", resp.Query)
		talkerLabel := resp.Talker
		if talkerLabel == "" {
			talkerLabel = "全部会话"
		}
		fmt.Fprintf(c.Writer, "会话: %s\n", talkerLabel)
		if resp.Sender != "" {
			fmt.Fprintf(c.Writer, "发送者: %s\n", resp.Sender)
		}
		switch {
		case !resp.Start.IsZero() && !resp.End.IsZero():
			fmt.Fprintf(c.Writer, "时间: %s ~ %s\n", resp.Start.Format("2006-01-02 15:04:05"), resp.End.Format("2006-01-02 15:04:05"))
		case !resp.Start.IsZero():
			fmt.Fprintf(c.Writer, "时间: >= %s\n", resp.Start.Format("2006-01-02 15:04:05"))
		case !resp.End.IsZero():
			fmt.Fprintf(c.Writer, "时间: <= %s\n", resp.End.Format("2006-01-02 15:04:05"))
		default:
			fmt.Fprintln(c.Writer, "时间: 不限")
		}
		fmt.Fprintf(c.Writer, "总命中: %d, 本页: %d\n", resp.Total, len(resp.Hits))
		fmt.Fprintln(c.Writer, strings.Repeat("-", 60))
		for idx, hit := range resp.Hits {
			if hit == nil || hit.Message == nil {
				continue
			}
			msg := hit.Message
			msg.SetContent("host", c.Request.Host)
			title := msg.Talker
			if msg.TalkerName != "" {
				title = fmt.Sprintf("%s (%s)", msg.TalkerName, msg.Talker)
			}
			sender := msg.Sender
			if msg.IsSelf {
				sender = "我"
			}
			if msg.SenderName != "" {
				sender = fmt.Sprintf("%s(%s)", msg.SenderName, msg.Sender)
			}
			fmt.Fprintf(c.Writer, "[%d] %s @ %s\n", idx+1, msg.Time.Format("2006-01-02 15:04:05"), title)
			fmt.Fprintf(c.Writer, "发送者: %s\n", sender)
			fmt.Fprintf(c.Writer, "%s\n", msg.PlainTextContent())
			if snippet := strings.TrimSpace(hit.Snippet); snippet != "" {
				fmt.Fprintf(c.Writer, "Snippet: %s\n", snippet)
			}
			fmt.Fprintln(c.Writer, strings.Repeat("-", 60))
		}
		return
	case "csv":
		c.Writer.Header().Set("Content-Type", "text/csv; charset=utf-8")
		c.Writer.Header().Set("Cache-Control", "no-cache")
		c.Writer.Header().Set("Connection", "keep-alive")
		c.Writer.Header().Set("Content-Disposition", fmt.Sprintf("attachment; filename=search_%s.csv", time.Now().Format("20060102_150405")))
		csvWriter := csv.NewWriter(c.Writer)
		csvWriter.Write([]string{"Seq", "Time", "Talker", "TalkerName", "Sender", "SenderName", "Content", "Snippet"})
		for _, hit := range resp.Hits {
			if hit == nil || hit.Message == nil {
				continue
			}
			msg := hit.Message
			msg.SetContent("host", c.Request.Host)
			csvWriter.Write([]string{
				fmt.Sprintf("%d", msg.Seq),
				msg.Time.Format("2006-01-02 15:04:05"),
				msg.Talker,
				msg.TalkerName,
				msg.Sender,
				msg.SenderName,
				msg.PlainTextContent(),
				strings.ReplaceAll(hit.Snippet, "\n", " "),
			})
		}
		csvWriter.Flush()
		return
	case "json":
		c.JSON(http.StatusOK, resp)
		return
	default:
		c.JSON(http.StatusOK, resp)
		return
	}
}

func (s *Service) handleChatlog(c *gin.Context) {
	q := struct {
		Time    string `form:"time"`
		Talker  string `form:"talker"`
		Sender  string `form:"sender"`
		Keyword string `form:"keyword"`
		Limit   int    `form:"limit"`
		Offset  int    `form:"offset"`
		Format  string `form:"format"`
	}{}

	if err := c.BindQuery(&q); err != nil {
		errors.Err(c, err)
		return
	}

	start, end, ok := util.TimeRangeOf(q.Time)
	if !ok {
		errors.Err(c, errors.InvalidArg("time"))
	}
	if q.Limit < 0 {
		q.Limit = 0
	}
	if q.Offset < 0 {
		q.Offset = 0
	}

	format := strings.ToLower(strings.TrimSpace(q.Format))
	if format == "" {
		format = "json"
	}

	// 1. 未指定 talker: 分组输出
	if q.Talker == "" {
		sessionsResp, err := s.db.GetSessions("", 0, 0)
		if err != nil {
			errors.Err(c, err)
			return
		}
		type grouped struct {
			Talker     string           `json:"talker"`
			TalkerName string           `json:"talkerName,omitempty"`
			Messages   []*model.Message `json:"messages"`
		}
		groups := make([]*grouped, 0)
		for _, sess := range sessionsResp.Items {
			msgs, err := s.db.GetMessages(start, end, sess.UserName, q.Sender, q.Keyword, 0, 0)
			if err != nil || len(msgs) == 0 {
				continue
			}
			groups = append(groups, &grouped{Talker: sess.UserName, TalkerName: sess.NickName, Messages: msgs})
		}
		switch format {
		case "html":
			c.Writer.Header().Set("Content-Type", "text/html; charset=utf-8")
			writeChatlogHTMLHeader(c.Writer, "Chatlog")
			c.Writer.WriteString(fmt.Sprintf("<h2>All Messages %s ~ %s</h2>", start.Format("2006-01-02 15:04:05"), end.Format("2006-01-02 15:04:05")))
			for _, g := range groups {
				title := g.Talker
				if g.TalkerName != "" {
					title = fmt.Sprintf("%s (%s)", g.TalkerName, g.Talker)
				}
				c.Writer.WriteString("<details open><summary>" + template.HTMLEscapeString(title) + fmt.Sprintf(" - %d 条消息</summary>", len(g.Messages)))
				for _, m := range g.Messages {
					m.SetContent("host", c.Request.Host)
					senderDisplay := m.Sender
					if m.IsSelf {
						senderDisplay = "我"
					}
					if m.SenderName != "" {
						senderDisplay = template.HTMLEscapeString(m.SenderName) + "(" + template.HTMLEscapeString(senderDisplay) + ")"
					} else {
						senderDisplay = template.HTMLEscapeString(senderDisplay)
					}
					aurl := template.HTMLEscapeString(s.composeAvatarURL(m.Sender) + "?size=big")
					timeText := template.HTMLEscapeString(m.Time.Format("2006-01-02 15:04:05"))
					c.Writer.WriteString("<div class=\"msg\"><div class=\"msg-row\"><img class=\"avatar\" src=\"" + aurl + "\" loading=\"lazy\" alt=\"avatar\" onerror=\"this.style.visibility='hidden'\"/><div class=\"msg-content\"><div class=\"meta\"><span class=\"sender\">" + senderDisplay + "</span><span class=\"time\">" + timeText + "</span></div><pre>" + messageHTMLPlaceholder(m) + "</pre></div></div></div>")
				}
				c.Writer.WriteString("</details>")
			}
			c.Writer.WriteString(previewHTMLSnippet)
			c.Writer.WriteString("</body></html>")
		case "json":
			c.JSON(http.StatusOK, groups)
		case "csv":
			c.Writer.Header().Set("Content-Type", "text/csv; charset=utf-8")
			c.Writer.Header().Set("Content-Disposition", fmt.Sprintf("attachment; filename=all_%s_%s.csv", start.Format("2006-01-02"), end.Format("2006-01-02")))
			c.Writer.Header().Set("Cache-Control", "no-cache")
			c.Writer.Header().Set("Connection", "keep-alive")
			c.Writer.Flush()
			csvWriter := csv.NewWriter(c.Writer)
			csvWriter.Write([]string{"Talker", "TalkerName", "Time", "SenderName", "Sender", "Content"})
			for _, g := range groups {
				for _, m := range g.Messages {
					csvWriter.Write([]string{g.Talker, g.TalkerName, m.Time.Format("2006-01-02 15:04:05"), m.SenderName, m.Sender, m.PlainTextContent()})
				}
			}
			csvWriter.Flush()
		case "text", "plain":
			c.Writer.Header().Set("Content-Type", "text/plain; charset=utf-8")
			c.Writer.Header().Set("Cache-Control", "no-cache")
			c.Writer.Header().Set("Connection", "keep-alive")
			c.Writer.Flush()
			for _, g := range groups {
				header := g.Talker
				if g.TalkerName != "" {
					header = fmt.Sprintf("%s (%s)", g.TalkerName, g.Talker)
				}
				c.Writer.WriteString(header + "\n")
				for _, m := range g.Messages {
					sender := m.Sender
					if m.IsSelf {
						sender = "我"
					}
					if m.SenderName != "" {
						sender = m.SenderName + "(" + sender + ")"
					}
					c.Writer.WriteString(m.Time.Format("2006-01-02 15:04:05") + " " + sender + " " + m.PlainTextContent() + "\n")
				}
				c.Writer.WriteString("-----------------------------\n")
			}
		default:
			c.JSON(http.StatusOK, groups)
		}
		return
	}

	// 2. 指定 talker: 单会话消息
	messages, err := s.db.GetMessages(start, end, q.Talker, q.Sender, q.Keyword, q.Limit, q.Offset)
	if err != nil {
		errors.Err(c, err)
		return
	}
	switch format {
	case "html":
		c.Writer.Header().Set("Content-Type", "text/html; charset=utf-8")
		writeChatlogHTMLHeader(c.Writer, "Chatlog")
		c.Writer.WriteString(fmt.Sprintf("<h2>Messages %s ~ %s (%s)</h2>", start.Format("2006-01-02 15:04:05"), end.Format("2006-01-02 15:04:05"), template.HTMLEscapeString(q.Talker)))
		for _, m := range messages {
			m.SetContent("host", c.Request.Host)
			c.Writer.WriteString("<div class=\"msg\"><div class=\"msg-row\">")
			aurl := template.HTMLEscapeString(s.composeAvatarURL(m.Sender) + "?size=big")
			c.Writer.WriteString("<img class=\"avatar\" src=\"" + aurl + "\" loading=\"lazy\" alt=\"avatar\" onerror=\"this.style.visibility='hidden'\"/>")
			c.Writer.WriteString("<div class=\"msg-content\"><div class=\"meta\"><span class=\"sender\">")
			if m.SenderName != "" {
				c.Writer.WriteString(template.HTMLEscapeString(m.SenderName) + "(")
			}
			c.Writer.WriteString(template.HTMLEscapeString(m.Sender))
			if m.SenderName != "" {
				c.Writer.WriteString(")")
			}
			timeText := template.HTMLEscapeString(m.Time.Format("2006-01-02 15:04:05"))
			c.Writer.WriteString("</span><span class=\"time\">" + timeText + "</span></div><pre>")
			c.Writer.WriteString(messageHTMLPlaceholder(m))
			c.Writer.WriteString("</pre></div></div></div>")
		}
		c.Writer.WriteString(previewHTMLSnippet)
		c.Writer.WriteString("</body></html>")
	case "csv":
		c.Writer.Header().Set("Content-Type", "text/csv; charset=utf-8")
		c.Writer.Header().Set("Content-Disposition", fmt.Sprintf("attachment; filename=%s_%s_%s.csv", q.Talker, start.Format("2006-01-02"), end.Format("2006-01-02")))
		c.Writer.Header().Set("Cache-Control", "no-cache")
		c.Writer.Header().Set("Connection", "keep-alive")
		c.Writer.Flush()
		csvWriter := csv.NewWriter(c.Writer)
		csvWriter.Write([]string{"Time", "SenderName", "Sender", "TalkerName", "Talker", "Content"})
		for _, m := range messages {
			csvWriter.Write(m.CSV(c.Request.Host))
		}
		csvWriter.Flush()
	case "json":
		c.JSON(http.StatusOK, messages)
	default:
		c.Writer.Header().Set("Content-Type", "text/plain; charset=utf-8")
		c.Writer.Header().Set("Cache-Control", "no-cache")
		c.Writer.Header().Set("Connection", "keep-alive")
		c.Writer.Flush()
		for _, m := range messages {
			c.Writer.WriteString(m.PlainText(strings.Contains(q.Talker, ","), util.PerfectTimeFormat(start, end), c.Request.Host) + "\n")
		}
	}
}

func (s *Service) handleContacts(c *gin.Context) {

	q := struct {
		Keyword string `form:"keyword"`
		Limit   int    `form:"limit"`
		Offset  int    `form:"offset"`
		Format  string `form:"format"`
	}{}

	if err := c.BindQuery(&q); err != nil {
		errors.Err(c, err)
		return
	}
	// 关键字去空白；空关键字表示返回全部
	q.Keyword = strings.TrimSpace(q.Keyword)

	list, err := s.db.GetContacts(q.Keyword, q.Limit, q.Offset)
	if err != nil {
		errors.Err(c, err)
		return
	}

	format := strings.ToLower(strings.TrimSpace(q.Format))
	if format == "" {
		format = "json"
	}
	switch format {
	case "html":
		c.Writer.Header().Set("Content-Type", "text/html; charset=utf-8")
		c.Writer.WriteHeader(http.StatusOK)
		c.Writer.Write([]byte(`<style>
  .contacts{font-family:Arial,Helvetica,sans-serif;font-size:14px;}
  .c-item{display:flex;align-items:center;gap:10px;border:1px solid #ddd;border-radius:6px;padding:6px 8px;margin:6px 0;background:#fff;box-shadow:0 1px 2px rgba(0,0,0,.04);} 
  .c-avatar{width:36px;height:36px;border-radius:50%;object-fit:cover;background:#f2f2f2;border:1px solid #eee}
  .c-name{font-weight:600;color:#2c3e50}
  .c-sub{color:#666;font-size:12px}
</style><div class="contacts">`))
		for _, contact := range list.Items {
			uname := template.HTMLEscapeString(contact.UserName)
			nick := template.HTMLEscapeString(contact.NickName)
			remark := template.HTMLEscapeString(contact.Remark)
			alias := template.HTMLEscapeString(contact.Alias)
			// compose avatar URL
			aurl := template.HTMLEscapeString(s.composeAvatarURL(contact.UserName))
			c.Writer.WriteString(`<div class="c-item">`)
			c.Writer.WriteString(`<img class="c-avatar" src="` + aurl + `" loading="lazy" onerror="this.style.visibility='hidden'"/>`)
			c.Writer.WriteString(`<div>`)
			c.Writer.WriteString(`<div class="c-name">` + nick + `</div>`)
			c.Writer.WriteString(`<div class="c-sub">` + uname)
			if remark != "" {
				c.Writer.WriteString(` · ` + remark)
			}
			if alias != "" {
				c.Writer.WriteString(` · alias:` + alias)
			}
			c.Writer.WriteString(`</div></div></div>`)
		}
		c.Writer.WriteString(`</div>`)
		return
	case "json":
		// fill avatar urls
		for _, item := range list.Items {
			item.AvatarURL = s.composeAvatarURL(item.UserName)
		}
		c.JSON(http.StatusOK, list)
	default:
		// csv
		if format == "csv" {
			// 浏览器访问时，会下载文件
			c.Writer.Header().Set("Content-Type", "text/csv; charset=utf-8")
		} else {
			c.Writer.Header().Set("Content-Type", "text/plain; charset=utf-8")
		}
		c.Writer.Header().Set("Cache-Control", "no-cache")
		c.Writer.Header().Set("Connection", "keep-alive")
		c.Writer.Flush()
		c.Writer.WriteString("UserName,Alias,Remark,NickName,AvatarURL\n")
		for _, contact := range list.Items {
			avatarURL := s.composeAvatarURL(contact.UserName)
			c.Writer.WriteString(fmt.Sprintf("%s,%s,%s,%s,%s\n", contact.UserName, contact.Alias, contact.Remark, contact.NickName, avatarURL))
		}
		c.Writer.Flush()
	}
}

// composeAvatarURL builds a relative URL that the server can serve for any username
func (s *Service) composeAvatarURL(username string) string {
	if username == "" {
		return ""
	}
	return "/avatar/" + username
}

// handleAvatar serves avatar by username. For v3 returns redirect to remote URL; for v4 streams bytes.
func (s *Service) handleAvatar(c *gin.Context) {
	username := c.Param("username")
	size := c.Query("size") // optional: small|big
	avatar, err := s.db.GetAvatar(username, size)
	if err != nil {
		errors.Err(c, err)
		return
	}
	if avatar == nil {
		errors.Err(c, errors.ErrAvatarNotFound)
		return
	}
	if avatar.URL != "" {
		// external URL, redirect
		c.Redirect(http.StatusFound, avatar.URL)
		return
	}
	// inline bytes
	ct := avatar.ContentType
	if ct == "" {
		ct = "image/jpeg"
	}
	c.Data(http.StatusOK, ct, avatar.Data)
}

func (s *Service) handleChatRooms(c *gin.Context) {

	q := struct {
		Keyword string `form:"keyword"`
		Limit   int    `form:"limit"`
		Offset  int    `form:"offset"`
		Format  string `form:"format"`
	}{}

	if err := c.BindQuery(&q); err != nil {
		errors.Err(c, err)
		return
	}
	// 关键字去空白；空关键字表示返回全部
	q.Keyword = strings.TrimSpace(q.Keyword)

	list, err := s.db.GetChatRooms(q.Keyword, q.Limit, q.Offset)
	if err != nil {
		errors.Err(c, err)
		return
	}
	format := strings.ToLower(strings.TrimSpace(q.Format))
	if format == "" {
		format = "json"
	}
	switch format {
	case "json":
		// json
		c.JSON(http.StatusOK, list)
	default:
		// csv
		if format == "csv" {
			// 浏览器访问时，会下载文件
			c.Writer.Header().Set("Content-Type", "text/csv; charset=utf-8")
		} else {
			c.Writer.Header().Set("Content-Type", "text/plain; charset=utf-8")
		}
		c.Writer.Header().Set("Cache-Control", "no-cache")
		c.Writer.Header().Set("Connection", "keep-alive")
		c.Writer.Flush()

		c.Writer.WriteString("Name,Remark,NickName,Owner,UserCount\n")
		for _, chatRoom := range list.Items {
			c.Writer.WriteString(fmt.Sprintf("%s,%s,%s,%s,%d\n", chatRoom.Name, chatRoom.Remark, chatRoom.NickName, chatRoom.Owner, len(chatRoom.Users)))
		}
		c.Writer.Flush()
	}
}

func (s *Service) handleSessions(c *gin.Context) {

	q := struct {
		Keyword string `form:"keyword"`
		Limit   int    `form:"limit"`
		Offset  int    `form:"offset"`
		Format  string `form:"format"`
	}{}

	if err := c.BindQuery(&q); err != nil {
		errors.Err(c, err)
		return
	}

	sessions, err := s.db.GetSessions(q.Keyword, q.Limit, q.Offset)
	if err != nil {
		errors.Err(c, err)
		return
	}
	format := strings.ToLower(strings.TrimSpace(q.Format))
	if format == "" {
		format = "json"
	}
	switch format {
	case "html":
		c.Writer.Header().Set("Content-Type", "text/html; charset=utf-8")
		c.Writer.WriteHeader(http.StatusOK)
		c.Writer.Write([]byte(`<style>
  .sessions-wrap{font-family:Arial,Helvetica,sans-serif;font-size:14px;line-height:1.5;}
  .session-item{border:1px solid #ddd;border-radius:6px;padding:8px 10px;margin:8px 0;background:#fff;box-shadow:0 1px 2px rgba(0,0,0,.04);} 
  .session-head{font-weight:600;color:#2c3e50;margin-bottom:4px;}
  .session-head .uname{color:#888;font-weight:400;margin-left:6px;}
  .session-time{color:#16a085;font-size:12px;margin-left:4px;}
  .session-content{margin-top:4px;white-space:pre-wrap;word-break:break-word;color:#333;}
</style><div class="sessions-wrap">`))
		for _, session := range sessions.Items {
			// 转义
			name := template.HTMLEscapeString(session.NickName)
			uname := template.HTMLEscapeString(session.UserName)
			content := template.HTMLEscapeString(session.Content)
			if len(content) > 400 { // 简单截断，避免过长
				content = content[:400] + "..."
			}
			content = strings.ReplaceAll(content, "\r", "")
			content = strings.ReplaceAll(content, "\n", "\n") // 让 pre-wrap 生效
			c.Writer.Write([]byte(`<div class="session-item"><div class="session-head">` + name + `<span class="uname">(` + uname + `)</span><span class="session-time">` + session.NTime.Format("2006-01-02 15:04:05") + `</span></div><div class="session-content">` + content + `</div></div>`))
		}
		c.Writer.Write([]byte(`</div>`))
		c.Writer.Write([]byte(previewHTMLSnippet))
		c.Writer.Flush()
		return
	case "csv":
		c.Writer.Header().Set("Content-Type", "text/csv; charset=utf-8")
		c.Writer.Header().Set("Cache-Control", "no-cache")
		c.Writer.Header().Set("Connection", "keep-alive")
		c.Writer.Flush()

		c.Writer.WriteString("UserName,NOrder,NickName,Content,NTime\n")
		for _, session := range sessions.Items {
			c.Writer.WriteString(fmt.Sprintf("%s,%d,%s,%s,%s\n", session.UserName, session.NOrder, session.NickName, strings.ReplaceAll(session.Content, "\n", "\\n"), session.NTime))
		}
		c.Writer.Flush()
	case "json":
		// json
		c.JSON(http.StatusOK, sessions)
	default:
		c.Writer.Header().Set("Content-Type", "text/plain; charset=utf-8")
		c.Writer.Header().Set("Cache-Control", "no-cache")
		c.Writer.Header().Set("Connection", "keep-alive")
		c.Writer.Flush()
		for _, session := range sessions.Items {
			c.Writer.WriteString(session.PlainText(120))
			c.Writer.WriteString("\n")
		}
		c.Writer.Flush()
	}
}

// handleDiary 返回指定日期内“我”参与的消息（日记），按 talker 分组。
// GET /api/v1/diary?date=YYYY-MM-DD&format=(html|json|csv|text)
func (s *Service) handleDiary(c *gin.Context) {
	q := struct {
		Date   string `form:"date"`
		Talker string `form:"talker"`
		Format string `form:"format"`
	}{}
	if err := c.BindQuery(&q); err != nil {
		errors.Err(c, err)
		return
	}

	dateStr := strings.TrimSpace(q.Date)
	if dateStr == "" {
		dateStr = time.Now().Format("2006-01-02")
	}

	parsed, err := time.ParseInLocation("2006-01-02", dateStr, time.Local)
	if err != nil {
		errors.Err(c, errors.InvalidArg("date"))
		return
	}
	start := time.Date(parsed.Year(), parsed.Month(), parsed.Day(), 0, 0, 0, 0, parsed.Location())
	end := start.Add(24*time.Hour - time.Nanosecond)

	startDisplay := start.Format("2006-01-02 15:04:05")
	endDisplay := end.Format("2006-01-02 15:04:05")
	heading := fmt.Sprintf("%s 的聊天日记（%s ~ %s）", start.Format("2006-01-02"), startDisplay, endDisplay)

	// 获取会话（可选 talker 过滤）
	sessionsResp, err := s.db.GetSessions(q.Talker, 0, 0)
	if err != nil {
		errors.Err(c, err)
		return
	}

	type grouped struct {
		Talker     string           `json:"talker"`
		TalkerName string           `json:"talkerName,omitempty"`
		Messages   []*model.Message `json:"messages"`
	}
	groups := make([]*grouped, 0)

	for _, sess := range sessionsResp.Items {
		msgs, err := s.db.GetMessages(start, end, sess.UserName, "", "", 0, 0)
		if err != nil || len(msgs) == 0 {
			continue
		}
		hasSelf := false
		for _, m := range msgs {
			if m.IsSelf {
				hasSelf = true
				break
			}
		}
		if !hasSelf {
			continue
		}
		groups = append(groups, &grouped{Talker: sess.UserName, TalkerName: sess.NickName, Messages: msgs})
	}

	format := strings.ToLower(strings.TrimSpace(q.Format))
	if format == "" {
		format = "json"
	}
	switch format {
	case "html":
		c.Writer.Header().Set("Content-Type", "text/html; charset=utf-8")
		c.Writer.WriteString(`<html><head><meta charset="utf-8"><title>Diary</title><style>body{font-family:Arial,Helvetica,sans-serif;font-size:14px;}details{margin:8px 0;padding:6px 8px;border:1px solid #ddd;border-radius:6px;background:#fafafa;}summary{cursor:pointer;font-weight:600;} .msg{margin:4px 0;padding:4px 6px;border-left:3px solid #2ecc71;background:#fff;} .msg-row{display:flex;gap:8px;align-items:flex-start;} .avatar{width:28px;height:28px;border-radius:6px;object-fit:cover;background:#f2f2f2;border:1px solid #eee;flex:0 0 28px} .msg-content{flex:1;min-width:0} .meta{color:#666;font-size:12px;margin-bottom:2px;} pre{white-space:pre-wrap;word-break:break-word;margin:0;} .sender{color:#27ae60;} .time{color:#16a085;margin-left:6px;} a.media{color:#2c3e50;text-decoration:none;} a.media:hover{text-decoration:underline;}</style></head><body>`)
		c.Writer.WriteString(fmt.Sprintf("<h2>%s</h2>", template.HTMLEscapeString(heading)))
		for _, g := range groups {
			title := g.Talker
			if g.TalkerName != "" {
				title = fmt.Sprintf("%s (%s)", g.TalkerName, g.Talker)
			}
			c.Writer.WriteString("<details open><summary>" + template.HTMLEscapeString(title) + fmt.Sprintf(" - %d 条消息</summary>", len(g.Messages)))
			for _, m := range g.Messages {
				m.SetContent("host", c.Request.Host)
				senderDisplay := m.Sender
				if m.IsSelf {
					senderDisplay = "我"
				}
				if m.SenderName != "" {
					senderDisplay = template.HTMLEscapeString(m.SenderName) + "(" + template.HTMLEscapeString(senderDisplay) + ")"
				} else {
					senderDisplay = template.HTMLEscapeString(senderDisplay)
				}
				aurl := template.HTMLEscapeString(s.composeAvatarURL(m.Sender) + "?size=big")
				c.Writer.WriteString("<div class=\"msg\"><div class=\"msg-row\"><img class=\"avatar\" src=\"" + aurl + "\" loading=\"lazy\" alt=\"avatar\" onerror=\"this.style.visibility='hidden'\"/><div class=\"msg-content\"><div class=\"meta\"><span class=\"sender\">" + senderDisplay + "</span><span class=\"time\">" + m.Time.Format("2006-01-02 15:04:05") + "</span></div><pre>" + messageHTMLPlaceholder(m) + "</pre></div></div></div>")
			}
			c.Writer.WriteString("</details>")
		}
		c.Writer.WriteString(previewHTMLSnippet)
		c.Writer.WriteString("</body></html>")
	case "json":
		c.JSON(http.StatusOK, groups)
	case "csv":
		c.Writer.Header().Set("Content-Type", "text/csv; charset=utf-8")
		c.Writer.Header().Set("Cache-Control", "no-cache")
		c.Writer.Header().Set("Connection", "keep-alive")
		c.Writer.Flush()
		writer := csv.NewWriter(c.Writer)
		writer.Write([]string{"Talker", "TalkerName", "Time", "SenderName", "Sender", "Content"})
		for _, g := range groups {
			for _, m := range g.Messages {
				writer.Write([]string{m.Talker, m.TalkerName, m.Time.Format("2006-01-02 15:04:05"), m.SenderName, m.Sender, m.PlainTextContent()})
			}
		}
		writer.Flush()
	default:
		c.Writer.Header().Set("Content-Type", "text/plain; charset=utf-8")
		c.Writer.Header().Set("Cache-Control", "no-cache")
		c.Writer.Header().Set("Connection", "keep-alive")
		c.Writer.Flush()
		for _, g := range groups {
			if g.TalkerName != "" {
				c.Writer.WriteString(fmt.Sprintf("%s (%s)\n", g.TalkerName, g.Talker))
			} else {
				c.Writer.WriteString(g.Talker + "\n")
			}
			for _, m := range g.Messages {
				senderDisplay := m.Sender
				if m.IsSelf {
					senderDisplay = "我"
				}
				if m.SenderName != "" {
					senderDisplay = m.SenderName + "(" + senderDisplay + ")"
				}
				c.Writer.WriteString(m.Time.Format("2006-01-02 15:04:05"))
				c.Writer.WriteString(" ")
				c.Writer.WriteString(senderDisplay)
				c.Writer.WriteString(" ")
				c.Writer.WriteString(m.PlainTextContent())
				c.Writer.WriteString("\n")
			}
			c.Writer.WriteString("-----------------------------\n")
		}
	}
}

func (s *Service) handleMedia(c *gin.Context, _type string) {
	key := strings.TrimPrefix(c.Param("key"), "/")
	if key == "" {
		errors.Err(c, errors.InvalidArg(key))
		return
	}

	keys := util.Str2List(key, ",")
	if len(keys) == 0 {
		errors.Err(c, errors.InvalidArg(key))
		return
	}

	var _err error
	for _, k := range keys {
		if strings.Contains(k, "/") {
			if absolutePath, err := s.findPath(_type, k); err == nil {
				c.Redirect(http.StatusFound, "/data/"+absolutePath)
				return
			}
		}
		media, err := s.db.GetMedia(_type, k)
		if err != nil {
			_err = err
			continue
		}
		if c.Query("info") != "" {
			c.JSON(http.StatusOK, media)
			return
		}
		if media.Type == "voice" && c.Query("transcribe") != "" {
			s.handleVoiceTranscription(c, k, media)
			return
		}
		switch media.Type {
		case "voice":
			s.HandleVoice(c, media.Data)
			return
		default:
			c.Redirect(http.StatusFound, "/data/"+media.Path)
			return
		}
	}

	if _err != nil {
		errors.Err(c, _err)
		return
	}
}

func (s *Service) handleVoiceTranscription(c *gin.Context, key string, media *model.Media) {
	if s.speechTranscriber == nil {
		c.JSON(http.StatusServiceUnavailable, gin.H{"error": "speech transcription not enabled"})
		return
	}

	if len(media.Data) == 0 {
		c.JSON(http.StatusInternalServerError, gin.H{"error": "voice data unavailable"})
		return
	}

	ctx := c.Request.Context()
	if ctx == nil {
		ctx = context.Background()
	}
	var cancel context.CancelFunc
	if _, hasDeadline := ctx.Deadline(); !hasDeadline {
		ctx, cancel = context.WithTimeout(ctx, 2*time.Minute)
	}
	if cancel != nil {
		defer cancel()
	}

	opts := s.speechOptions
	if lang := strings.TrimSpace(c.Query("lang")); lang != "" {
		opts.Language = lang
		opts.LanguageSet = true
	}
	if translate := strings.TrimSpace(c.Query("translate")); translate != "" {
		switch strings.ToLower(translate) {
		case "1", "true", "yes", "on":
			opts.Translate = true
			opts.TranslateSet = true
		case "0", "false", "no", "off":
			opts.Translate = false
			opts.TranslateSet = true
		}
	}

	res, err := s.speechTranscriber.TranscribeSilk(ctx, media.Data, opts)
	if err != nil {
		if ctx.Err() != nil {
			c.JSON(http.StatusRequestTimeout, gin.H{"error": "transcription cancelled"})
			return
		}
		log.Error().Err(err).Str("media_key", key).Msg("voice transcription failed")
		c.JSON(http.StatusInternalServerError, gin.H{"error": "transcription failed"})
		return
	}
	if res == nil {
		c.JSON(http.StatusOK, gin.H{"key": key, "text": "", "language": opts.Language, "duration": 0})
		return
	}

	c.JSON(http.StatusOK, gin.H{
		"key":      key,
		"text":     res.Text,
		"language": res.Language,
		"duration": res.Duration.Seconds(),
		"segments": res.Segments,
	})
}

func (s *Service) findPath(_type string, key string) (string, error) {
	absolutePath := filepath.Join(s.conf.GetDataDir(), key)
	if _, err := os.Stat(absolutePath); err == nil {
		return key, nil
	}
	switch _type {
	case "image":
		for _, suffix := range []string{"_h.dat", ".dat", "_t.dat"} {
			if _, err := os.Stat(absolutePath + suffix); err == nil {
				return key + suffix, nil
			}
		}
	case "video":
		for _, suffix := range []string{".mp4", "_thumb.jpg"} {
			if _, err := os.Stat(absolutePath + suffix); err == nil {
				return key + suffix, nil
			}
		}
	}
	return "", errors.ErrMediaNotFound
}

func (s *Service) handleMediaData(c *gin.Context) {
	relativePath := filepath.Clean(c.Param("path"))

	absolutePath := filepath.Join(s.conf.GetDataDir(), relativePath)

	if _, err := os.Stat(absolutePath); os.IsNotExist(err) {
		c.JSON(http.StatusNotFound, gin.H{
			"error": "File not found",
		})
		return
	}

	ext := strings.ToLower(filepath.Ext(absolutePath))
	switch {
	case ext == ".dat":
		s.HandleDatFile(c, absolutePath)
	default:
		// 直接返回文件
		c.File(absolutePath)
	}

}

func (s *Service) HandleDatFile(c *gin.Context, path string) {

	b, err := os.ReadFile(path)
	if err != nil {
		errors.Err(c, err)
		return
	}
	out, ext, err := dat2img.Dat2Image(b)
	if err != nil {
		c.File(path)
		return
	}

	switch ext {
	case "jpg", "jpeg":
		c.Data(http.StatusOK, "image/jpeg", out)
	case "png":
		c.Data(http.StatusOK, "image/png", out)
	case "gif":
		c.Data(http.StatusOK, "image/gif", out)
	case "bmp":
		c.Data(http.StatusOK, "image/bmp", out)
	case "mp4":
		c.Data(http.StatusOK, "video/mp4", out)
	default:
		c.Data(http.StatusOK, "image/jpg", out)
		// c.File(path)
	}
}

func (s *Service) HandleVoice(c *gin.Context, data []byte) {
	out, err := silk.Silk2MP3(data)
	if err != nil {
		c.Data(http.StatusOK, "audio/silk", data)
		return
	}
	c.Data(http.StatusOK, "audio/mp3", out)
}

// 统一占位符：将 PlainTextContent 里形如 ![标签](url) 或 [标签](url) 的模式转成超链接形式，仅显示 [标签]。
var (
	placeholderPattern = regexp.MustCompile(`!?\[([^\]]+)\]\((https?://[^)]+)\)`)
)

func messageHTMLPlaceholder(m *model.Message) string {
	content := m.PlainTextContent()
	return placeholderPattern.ReplaceAllStringFunc(content, func(s string) string {
		matches := placeholderPattern.FindStringSubmatch(s)
		if len(matches) != 3 {
			return template.HTMLEscapeString(s)
		}
		fullLabel := matches[1]
		url := matches[2]
		left := fullLabel
		rest := ""
		if p := strings.Index(fullLabel, "|"); p >= 0 {
			left = fullLabel[:p]
			rest = fullLabel[p+1:]
		}
		className := "media"
		if left == "动画表情" || left == "GIF表情" || strings.Contains(left, "表情") {
			className = "media anim"
		}
		if left == "语音" {
			className = "media voice-link"
		}
		var anchorText string
		if left == "链接" { // 保留完整形式 [链接|标题\n更多说明]
			escapedFull := template.HTMLEscapeString(fullLabel)
			escapedFull = strings.ReplaceAll(escapedFull, "\r", "")
			escapedFull = strings.ReplaceAll(escapedFull, "\n", "<br/>")
			anchorText = "[" + escapedFull + "]"
		} else if left == "文件" && rest != "" { // 文件保留文件名
			anchorText = "[文件]" + template.HTMLEscapeString(rest)
		} else {
			anchorText = "[" + template.HTMLEscapeString(left) + "]"
		}
		escapedURL := template.HTMLEscapeString(url)
		anchor := `<a class="` + className + `" href="` + escapedURL + `" target="_blank">` + anchorText + `</a>`
		if left == "语音" {
			return `<span class="voice-entry">` + anchor + `<button type="button" class="voice-transcribe-btn">转文字</button><span class="voice-transcribe-result" aria-live="polite"></span></span>`
		}
		return anchor
	})
}
