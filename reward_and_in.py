from __future__ import annotations
import os
import re
import asyncio
import logging
from datetime import datetime, timedelta, time
from zoneinfo import ZoneInfo
from typing import Optional, List, Dict, Any, Tuple, Iterable, AsyncGenerator
from contextlib import asynccontextmanager
from collections import defaultdict

import discord
from discord.ext import commands, tasks
from discord import app_commands
import aiosqlite
from dotenv import load_dotenv
import io
from wcwidth import wcswidth
import math

# --- 設定 ---
load_dotenv()
TOKEN: str = os.getenv("DISCORD_BOT_TOKEN", "")
DB_FILE: str = os.getenv("DB_FILE", "voice_activity.db")
# 元のコードからIDをデフォルト値として設定
TEST_CHANNEL_ID: int = int(os.getenv("TEST_CHANNEL_ID", "1329341560256467045"))
DISBOARD_BOT_ID: int = int(os.getenv("DISBOARD_BOT_ID", "302050872383242240"))

# --- ロールIDリスト (環境変数がなければデフォルト値を使用) ---
male_roles_str = os.getenv("MALE_ROLES", "812663143654096946,784723518402592805")
MALE_ROLES: List[int] = [int(role_id) for role_id in male_roles_str.split(",") if role_id.strip()]

female_roles_str = os.getenv("FEMALE_ROLES", "812698196098154538,784723518402592804")
FEMALE_ROLES: List[int] = [int(role_id) for role_id in female_roles_str.split(",") if role_id.strip()]

NEWCOMER_ROLE_ID: int = int(os.getenv("NEWCOMER_ROLE_ID", "784723518402592803"))

extra_admin_roles_str = os.getenv("EXTRA_ADMIN_ROLES", "784723518809178135,991112832655560825,784723518809178134")
EXTRA_ADMIN_ROLES: List[int] = [int(role_id) for role_id in extra_admin_roles_str.split(",") if role_id.strip()]
# --- 皆勤賞用 追加ロール ---------------------------------
EXTRA_ATTEND_MALE_ROLE_ID: int = 973947567018737664  # 男性枠にカウント
EXTRA_ATTEND_FEMALE_ROLE_ID: int = 973947299279560785  # 女性枠にカウント
# ---------------------------------------------------------
ADDITIONAL_REWARD_CHANNELS: list[int] = [  # ★ 皆勤賞用に追加したい VC
    927802462943997962,
    1319999130759598110,
]
MAX_ROWS_PER_COL = 25  # ★ 1 列あたりの最大メンバー数
COL_GAP_PX = 40  # 列間スペース

# --- レポート除外ロール (環境変数優先) ---
REPORT_EXCLUDE_ROLES_STR = os.getenv("REPORT_EXCLUDE_ROLES", "")  # デフォルトは空
REPORT_EXCLUDE_ROLES: set[int] = set()
if REPORT_EXCLUDE_ROLES_STR:
    try:
        roles_to_exclude = {int(role_id) for role_id in REPORT_EXCLUDE_ROLES_STR.split(",") if role_id.strip()}
        REPORT_EXCLUDE_ROLES = roles_to_exclude
        logging.info(f"レポート除外ロールを {len(REPORT_EXCLUDE_ROLES)} 件読み込みました: {REPORT_EXCLUDE_ROLES}")
    except ValueError:
        logging.error(
            "環境変数 REPORT_EXCLUDE_ROLES の形式が正しくありません。数値でないIDが含まれている可能性があります。")

# --- チャンネルIDリスト (環境変数がなければデフォルト値を使用) ---
TARGET_VC_CHANNELS_STR = os.getenv("TARGET_VC_CHANNELS", "")
REWARD_VC_CHANNELS_STR = os.getenv("REWARD_VC_CHANNELS", "")

if TARGET_VC_CHANNELS_STR is None: raise ValueError("環境変数 TARGET_VC_CHANNELS が設定されていません。")
if REWARD_VC_CHANNELS_STR is None: raise ValueError("環境変数 REWARD_VC_CHANNELS が設定されていません。")

try:
    TARGET_VC_CHANNELS: List[int] = [int(ch_id) for ch_id in TARGET_VC_CHANNELS_STR.split(",") if ch_id.strip()]
except ValueError:
    logging.error(f"環境変数 TARGET_VC_CHANNELS ('{TARGET_VC_CHANNELS_STR}') の形式エラー。")
    raise ValueError("環境変数 TARGET_VC_CHANNELS の形式が正しくありません。")

try:
    REWARD_VC_CHANNELS: List[int] = [int(ch_id) for ch_id in REWARD_VC_CHANNELS_STR.split(",") if ch_id.strip()]
except ValueError:
    logging.error(f"環境変数 REWARD_VC_CHANNELS ('{REWARD_VC_CHANNELS_STR}') の形式エラー。")
    raise ValueError("環境変数 REWARD_VC_CHANNELS の形式が正しくありません。")

GUILD_ID: int = int(os.getenv("GUILD_ID", "784723518402592799"))
WELC_MALE_ROLE: int = int(os.getenv("WELC_MALE_ROLE", "422683060501348354"))
WELC_FEMALE_ROLE: int = int(os.getenv("WELC_FEMALE_ROLE", "1102138920050901144"))
SPECIAL_ROLE_ID: int = int(os.getenv("SPECIAL_ROLE_ID", "1289488152301539339"))

ALL_TRACKED_CHANNELS: set[int] = set(TARGET_VC_CHANNELS + REWARD_VC_CHANNELS)
profile_channels_str = os.getenv("PROFILE_CHANNELS", "")
if not profile_channels_str:
    raise ValueError("環境変数 PROFILE_CHANNELS が設定されていません。")
PROFILE_CHANNELS: set[int] = {int(ch_id) for ch_id in profile_channels_str.split(",") if ch_id.strip()}

MAIN_REPORT_CHANNEL_ID: int = int(os.getenv("MAIN_REPORT_CHANNEL_ID", "1135406110178811934"))
INACTIVE_REPORT_CHANNEL_ID: int = int(os.getenv("INACTIVE_REPORT_CHANNEL_ID", "1149358069055229983"))

logging.basicConfig(level=logging.DEBUG, format="%(asctime)s - %(levelname)s - %(message)s",
                    handlers=[logging.FileHandler("bot.log", mode="a", encoding="utf-8"), logging.StreamHandler()])


# --- グローバルヘルパー ---
def ovlp_sec(s1: datetime, e1: datetime, s2: datetime, e2: datetime) -> float:
    """2区間の重複秒数"""
    if s1.tzinfo != e1.tzinfo or s2.tzinfo != e2.tzinfo or s1.tzinfo != s2.tzinfo:
        utc = ZoneInfo("UTC")
        s1 = (s1 if s1.tzinfo else s1.replace(tzinfo=utc)).astimezone(utc)
        e1 = (e1 if e1.tzinfo else e1.replace(tzinfo=utc)).astimezone(utc)
        s2 = (s2 if s2.tzinfo else s2.replace(tzinfo=utc)).astimezone(utc)
        e2 = (e2 if e2.tzinfo else e2.replace(tzinfo=utc)).astimezone(utc)
    overlap_start, overlap_end = max(s1, s2), min(e1, e2)
    return max(0, (overlap_end - overlap_start).total_seconds())


# --- 共通処理 ---
class TimeMgr:
    JST, UTC = ZoneInfo("Asia/Tokyo"), ZoneInfo("UTC")

    @staticmethod
    def now_utc() -> datetime:
        return datetime.now(TimeMgr.UTC)

    @staticmethod
    def now_jst() -> datetime:
        return datetime.now(TimeMgr.JST)

    # タイムゾーン未指定(naive)の場合はUTCとみなして変換
    @staticmethod
    def to_utc(dt: datetime) -> datetime:
        if dt.tzinfo is None: return dt.replace(tzinfo=TimeMgr.UTC)
        return dt.astimezone(TimeMgr.UTC)

    # タイムゾーン未指定(naive)の場合はJSTとみなして変換
    @staticmethod
    def to_jst(dt: datetime) -> datetime:
        if dt.tzinfo is None: return dt.replace(tzinfo=TimeMgr.JST)
        return dt.astimezone(TimeMgr.JST)


BOT_START_JST = TimeMgr.now_jst()


class Util:
    @staticmethod
    def dtStr(dt: datetime) -> str:
        return TimeMgr.to_utc(dt).strftime("%Y-%m-%d %H:%M:%S")

    @staticmethod
    def fmtDur(sec: int) -> str:
        sec = int(sec);
        h, rem = divmod(sec, 3600);
        m, s = divmod(rem, 60)
        parts = [f"{val}{unit}" for val, unit in zip([h, m, s], ["時間", "分", "秒"]) if val]
        return "".join(parts) if parts else "0秒"

    @staticmethod
    def splitChunks(text: str, size: int = 2000) -> List[str]:
        chunks, current = [], "";
        lines = text.splitlines(keepends=True)
        for line in lines:
            if len(current) + len(line) <= size:
                current += line
            else:
                if current: chunks.append(current)
                while len(line) > size: chunks.append(line[:size]); line = line[size:]
                current = line
        if current: chunks.append(current)
        return chunks or [""]

    @staticmethod
    def splitEmbed(text: str, limit: int = 1024) -> List[str]:
        return Util.splitChunks(text, size=limit)

    @staticmethod
    def parseUTC(dt_str: str) -> datetime:
        try:
            return datetime.strptime(dt_str, "%Y-%m-%d %H:%M:%S").replace(tzinfo=TimeMgr.UTC)
        except ValueError:
            logging.error(f"UTC日時文字列の解析失敗: {dt_str}"); return datetime.min.replace(tzinfo=TimeMgr.UTC)

    @staticmethod
    def listOrNone(items: Iterable[Any]) -> str:
        lst = [str(item) for item in items] if items else []; return ", ".join(lst) if lst else "該当者なし"

    @staticmethod
    def splitSessDay(
            start: datetime,
            end: datetime,
            *,
            tz: ZoneInfo = TimeMgr.JST,  # デフォルト JST
    ) -> List[Tuple[str, datetime, datetime]]:
        """
        1 セッションを “1 日＝tz の 0:00〜24:00” 単位で分割し、
        (キー(日付文字列), 区間開始(UTC), 区間終了(UTC)) のリストを返す。
        """
        segs: List[Tuple[str, datetime, datetime]] = []

        # 呼び出し元が tz 付き日時を渡してくるので、その tz を尊重
        st_tz = start.astimezone(tz)
        ed_tz = end.astimezone(tz)
        cur = st_tz

        while cur < ed_tz:
            day_start = cur.replace(hour=0, minute=0, second=0, microsecond=0)
            day_end = day_start + timedelta(days=1)

            seg_start = max(cur, day_start)
            seg_end = min(ed_tz, day_end)
            if seg_end > seg_start:
                segs.append((
                    day_start.strftime("%Y-%m-%d"),  # ← JST の日付キー
                    seg_start.astimezone(TimeMgr.UTC),  # 保存は UTC
                    seg_end.astimezone(TimeMgr.UTC),
                ))
            cur = seg_end

        return segs

    @staticmethod
    def getWkendPeriods(start_jst: datetime, end_jst: datetime) -> List[Tuple[datetime, datetime]]:
        per = [];
        current_date = start_jst.date()
        first_friday_date = current_date + timedelta(days=((4 - current_date.weekday() + 7) % 7))
        cur = datetime.combine(first_friday_date, time(17, 0, 0), tzinfo=TimeMgr.JST)
        while cur < end_jst:
            weekend_start = cur;
            weekend_end = (cur + timedelta(days=2)).replace(hour=0, minute=0, second=0, microsecond=0) + timedelta(
                days=1)
            overlap_start, overlap_end = max(weekend_start, start_jst), min(weekend_end, end_jst)
            if overlap_end > overlap_start: per.append((overlap_start, overlap_end))
            cur += timedelta(days=7)
        return per

    @staticmethod
    async def getSessAtTime(bot: "MyBot", query_utc: datetime) -> List[Tuple[int, int]]:
        qs = Util.dtStr(query_utc);
        results = []
        if not bot.db: return results
        async with bot.db_lock:
            async with bot.db.execute(
                "SELECT user_id, channel_id FROM voice_session_logs WHERE session_end > ? AND session_start < ?",
                (qs, qs)) as cur1: results.extend(await cur1.fetchall())
            async with bot.db.execute(
                "SELECT user_id, channel_id FROM voice_session_logs_reward WHERE session_end > ? AND session_start < ?",
                (qs, qs)) as cur2: results.extend(await cur2.fetchall())
        return results


# --- DBヘルパー ---
class DBH:
    @staticmethod
    async def setupDB(db_file: str) -> aiosqlite.Connection:
        """
        SQLite 接続を生成し、競合回避設定を行う。
        - WAL で読書並列化
        - locking_mode は NORMAL に戻す
        - busy_timeout で他プロセスロック時に待機
        """
        # ★ timeout=30 で 30 秒はロック解放を待つ
        conn = await aiosqlite.connect(
            db_file,
            isolation_level=None,
            timeout=30.0,  # デフォルト 5 秒 → 30 秒へ延長
        )

        # ---- PRAGMA 設定 ----
        await conn.execute("PRAGMA journal_mode=WAL;")  # WAL を継続
        await conn.execute("PRAGMA synchronous=NORMAL;")
        await conn.execute("PRAGMA cache_size = -20000;")  # 20 MB
        await conn.execute("PRAGMA temp_store = MEMORY;")
        # locking_mode=EXCLUSIVE は競合要因なので削除
        await conn.execute("PRAGMA busy_timeout = 30000;")  # ms 単位 (30 秒)

        conn.row_factory = aiosqlite.Row
        return conn

    @staticmethod
    async def initDB(conn: aiosqlite.Connection) -> None:
        queries = [
            "CREATE TABLE IF NOT EXISTS voice_session_logs (user_id INTEGER NOT NULL, channel_id INTEGER NOT NULL, session_start TEXT NOT NULL, session_end TEXT NOT NULL, duration INTEGER NOT NULL DEFAULT 0)",
            "CREATE TABLE IF NOT EXISTS voice_session_logs_reward (user_id INTEGER NOT NULL, channel_id INTEGER NOT NULL, session_start TEXT NOT NULL, session_end TEXT NOT NULL, duration INTEGER NOT NULL DEFAULT 0)",
            "CREATE TABLE IF NOT EXISTS newcomer_role_log (user_id INTEGER PRIMARY KEY, assigned_at TEXT NOT NULL)",
            "CREATE TABLE IF NOT EXISTS monthly_award_history (guild_id INTEGER NOT NULL, year INTEGER NOT NULL, month INTEGER NOT NULL, award_name TEXT NOT NULL, user_id INTEGER NOT NULL, value REAL NOT NULL DEFAULT 0, PRIMARY KEY (guild_id, year, month, award_name, user_id))",
            "CREATE TABLE IF NOT EXISTS inactivity_tracking (id INTEGER PRIMARY KEY CHECK (id = 1), user_ids TEXT NOT NULL DEFAULT '')",
            "CREATE TABLE IF NOT EXISTS profile_submission_log (user_id INTEGER PRIMARY KEY, submitted_at TEXT NOT NULL)",
            "CREATE TABLE IF NOT EXISTS room_craftsman_sessions (user_id INTEGER NOT NULL, channel_id INTEGER NOT NULL, session_start TEXT NOT NULL, session_end TEXT NOT NULL, together_duration INTEGER NOT NULL DEFAULT 0, join_count INTEGER NOT NULL DEFAULT 0, score INTEGER NOT NULL DEFAULT 0)",
            "CREATE TABLE IF NOT EXISTS reward_exclusions (guild_id INTEGER NOT NULL, user_id INTEGER NOT NULL, reason TEXT, added_at TEXT NOT NULL, PRIMARY KEY (guild_id, user_id))",
            "INSERT OR IGNORE INTO inactivity_tracking (id, user_ids) VALUES (1, '')"
        ]
        indices = [
            "CREATE INDEX IF NOT EXISTS idx_vsl_end ON voice_session_logs(session_end);",
            "CREATE INDEX IF NOT EXISTS idx_vslr_end ON voice_session_logs_reward(session_end);",
            "CREATE INDEX IF NOT EXISTS idx_mah_gymu ON monthly_award_history(guild_id, year, month, user_id);",
            "CREATE INDEX IF NOT EXISTS idx_psl_uid ON profile_submission_log(user_id);",
            "CREATE INDEX IF NOT EXISTS idx_rcs_end ON room_craftsman_sessions(session_end);"
        ]
        async with conn.cursor() as cursor:
            for query in queries + indices: await cursor.execute(query)
        logging.info("Database initialized/checked successfully.")

    @staticmethod
    async def fetchAll(conn: aiosqlite.Connection, query: str, params: tuple = ()) -> List[aiosqlite.Row]:
        async with conn.execute(query, params) as cursor: return await cursor.fetchall()

    @staticmethod
    async def fetchOne(conn: aiosqlite.Connection, query: str, params: tuple = ()) -> Optional[aiosqlite.Row]:
        async with conn.execute(query, params) as cursor: return await cursor.fetchone()

    @staticmethod
    async def execQuery(db: aiosqlite.Connection, lock: asyncio.Lock, query: str, params: tuple = ()) -> None:
        async with lock:
            try:
                await db.execute(query, params)
            except Exception as e:
                logging.exception(f"DB query failed: {query} with {params}")
                raise e


@asynccontextmanager
async def dbTxn(db: Optional[aiosqlite.Connection], lock: asyncio.Lock) -> AsyncGenerator[aiosqlite.Connection, None]:
    if db is None:
        logging.error("dbTxn called with db=None")
        raise ValueError("Database connection is None, cannot start transaction.")

    await lock.acquire()
    try:
        yield db
    except Exception as e:
        logging.exception("DB transaction failed, rolling back.")
        try:
            await db.rollback()
        except Exception as rb_exc:
            logging.error(f"CRITICAL: Failed to rollback transaction after an error: {rb_exc}")
        raise e
    finally:
        if lock.locked():
            lock.release()


# --- メンバー情報 ---
def getSex(member: Optional[discord.Member]) -> Optional[str]:
    if not member: return None
    rids = {r.id for r in member.roles}
    if any(rid in MALE_ROLES for rid in rids): return "male"
    if any(rid in FEMALE_ROLES for rid in rids): return "female"
    return None


def getWelSex(member: Optional[discord.Member]) -> Optional[str]:
    if not member: return None
    rids = {r.id for r in member.roles}
    if WELC_MALE_ROLE in rids: return "male"
    if WELC_FEMALE_ROLE in rids: return "female"
    return None


async def getNewDate(bot: MyBot, uid: int) -> Optional[datetime]:
    if not bot.db: return None
    async with bot.db_lock: row = await DBH.fetchOne(bot.db,
                                                     "SELECT submitted_at FROM profile_submission_log WHERE user_id = ?",
                                                     (uid,))
    return Util.parseUTC(row['submitted_at']) if row and row['submitted_at'] else None


async def recProfSub(bot: MyBot, uid: int, submission_time_utc: datetime) -> None:
    """
    すでに提出済みなら何もしない（再投稿・編集は無視）。
    """
    if not bot.db:
        return

    async with bot.db_lock:
        await bot.db.execute(
            # 既存行があれば INSERT を無視する
            "INSERT OR IGNORE INTO profile_submission_log (user_id, submitted_at) "
            "VALUES (?, ?)",
            (uid, Util.dtStr(submission_time_utc)),
        )


# --- Bot本体 ---
class MyBot(commands.Bot):
    def __init__(self, **kwargs) -> None:
        super().__init__(**kwargs)
        self.db: Optional[aiosqlite.Connection] = None
        self.db_lock: asyncio.Lock = asyncio.Lock()
        self.previous_inactive_members: set[int] = set()
        self.voice_state_tracking: Dict[int, Dict[str, Any]] = {}
        self.room_craftsman_sessions: Dict[int, Dict[str, Any]] = {}

    async def setup_hook(self) -> None:

        # --- DB 初期化 --------------------------------------------------
        self.db = await DBH.setupDB(DB_FILE)
        await DBH.initDB(self.db)

        # --- Cog 登録 ---------------------------------------------------
        reward_cog = RewardCmd(self)
        await self.add_cog(reward_cog)  # ← これだけで十分
        await setup_attendance_board(self)

        # --- ギルド限定化 ----------------------------------------------
        guild_obj = discord.Object(id=GUILD_ID)

        # ★【修正】戻り値は使わない -------------------------
        self.tree.copy_global_to(guild=guild_obj)
        logging.info(f"Copied global cmds to Guild {GUILD_ID}")
        # -----------------------------------------------

        # reward_exclude グループもギルド限定で追加
        self.tree.add_command(reward_exclude_group, guild=guild_obj)

        # --- 同期 -------------------------------------------------------
        synced = await self.tree.sync(guild=guild_obj)
        logging.info(f"Synced {len(synced)} commands to Guild {GUILD_ID}")

        # --- 周期タスク起動など ----------------------------------------
        self.reportLoop.start()
        self.midMonthLoop = self.loop.create_task(midMonthLoop(self))
        self.mthAwdLoop = self.loop.create_task(mthAwdLoop(self))
        logging.info("Bot setup_hook 完了 (すべてギルド限定)")

    @tasks.loop(hours=1)
    async def reportLoop(self):
        try:
            guild = self.get_guild(GUILD_ID)
            if not guild: logging.warning("[Report Task] Target guild not found."); return
            main_ch = guild.get_channel(MAIN_REPORT_CHANNEL_ID);
            inactive_ch = guild.get_channel(INACTIVE_REPORT_CHANNEL_ID)
            if not isinstance(main_ch, discord.TextChannel) or not isinstance(inactive_ch,
                                                                              discord.TextChannel): logging.warning(
                "[Report Task] Report channels not found or invalid."); return

            now_utc = TimeMgr.now_utc();
            start_utc_7d = now_utc - timedelta(days=7);
            four_days_ago_utc = now_utc - timedelta(days=4)
            logs_7d = []
            try:
                async with self.db_lock:
                    query = "SELECT user_id, session_start, session_end, duration FROM voice_session_logs WHERE session_end > ? UNION ALL SELECT user_id, session_start, session_end, duration FROM voice_session_logs_reward WHERE session_end > ?"
                    logs_7d = await DBH.fetchAll(self.db, query, (Util.dtStr(start_utc_7d), Util.dtStr(start_utc_7d)))
            except Exception:
                logging.exception("[Report Task] Failed to fetch session logs."); return

            user_logs: Dict[int, List[Dict[str, Any]]] = defaultdict(list)
            for row in logs_7d:
                try:
                    user_logs[row['user_id']].append(
                        {"start": Util.parseUTC(row['session_start']), "end": Util.parseUTC(row['session_end']),
                         "duration": row['duration'] or 0})
                except Exception as e:
                    logging.warning(f"[Report Task] Skipping invalid log entry for user {row['user_id']}: {row} - {e}")

            target_role_ids = set(MALE_ROLES + FEMALE_ROLES + [WELC_MALE_ROLE, WELC_FEMALE_ROLE])
            target_members = [m for m in guild.members if
                              not m.bot and any(r.id in target_role_ids for r in m.roles) and not any(
                                  r.id in REPORT_EXCLUDE_ROLES for r in m.roles)]
            stats_list = [];
            current_inactive_uids = set();
            now_jst = TimeMgr.to_jst(now_utc)

            for member in target_members:
                uid = member.id;
                is_special = any(r.id == SPECIAL_ROLE_ID for r in member.roles)
                joined_at_jst = TimeMgr.to_jst(member.joined_at) if member.joined_at else now_jst
                is_new = (now_jst - joined_at_jst) <= timedelta(days=7)
                member_sessions = user_logs.get(uid, [])
                last_call_utc = max((s["end"] for s in member_sessions), default=None) if member_sessions else None
                profile_submitted_utc = await getNewDate(self, uid)
                is_inactive = bool(profile_submitted_utc and profile_submitted_utc <= four_days_ago_utc and (
                            not last_call_utc or last_call_utc < four_days_ago_utc))
                if is_inactive: current_inactive_uids.add(uid)
                last_call_jst_str = TimeMgr.to_jst(last_call_utc).strftime("%m/%d %H:%M") if last_call_utc else "N/A"
                call_day_count = len({s["start"].date() for s in member_sessions})
                total_duration_sec = sum(s["duration"] for s in member_sessions)
                stats_list.append(
                    {"member": member, "last_call_utc": last_call_utc, "last_call_jst_str": last_call_jst_str,
                     "call_day_count": call_day_count, "total_hours": total_duration_sec // 3600,
                     "is_special": is_special, "is_new": is_new, "is_inactive": is_inactive})

            # --- メインレポート ---
            stats_list.sort(key=lambda s: (-s["call_day_count"], -s["total_hours"], s["member"].display_name))
            main_report_lines = ["【過去7日間 通話統計】", f"{'日数':<4}{'時間':<6}{'最終通話':<12} メンバー",
                                 "-" * 50] + ([
                                                  f"{s['call_day_count']:<4}{s['total_hours']:<6}{s['last_call_jst_str']:<12} {s['member'].mention}{(' ☆' if s['is_special'] else '')}{(' 〇' if s['is_new'] else '')}"
                                                  for s in stats_list] if stats_list else [
                "対象メンバーの通話記録がありません。"])
            try:
                await main_ch.purge(limit=10);
                [await main_ch.send(chunk) for chunk in Util.splitChunks("\n".join(main_report_lines))]
                logging.info("[Report Task] Sent main report.")
            except Exception:
                logging.exception("[Report Task] Failed to send main report.")

            # --- 非アクティブレポート ---
            inactive_members_stats = sorted([s for s in stats_list if s["is_inactive"]],
                                            key=lambda s: s["last_call_utc"] or datetime.min.replace(
                                                tzinfo=TimeMgr.UTC))
            inactive_report_lines = ["【4日以上通話なし (プロフィール提出4日経過者)】", "-" * 50] + ([
                                                                                                       f"{s['last_call_jst_str']:<12} {s['member'].mention}{(' ☆' if s['is_special'] else '')}{(' 〇' if s['is_new'] else '')}"
                                                                                                       for s in
                                                                                                       inactive_members_stats] if inactive_members_stats else [
                "該当者はいません。"])
            try:
                await inactive_ch.purge(limit=10);
                [await inactive_ch.send(chunk) for chunk in Util.splitChunks("\n".join(inactive_report_lines))]
                logging.info("[Report Task] Sent inactive report.")
            except Exception:
                logging.exception("[Report Task] Failed to send inactive report.")

            # --- DB保存 ---
            try:
                async with self.db_lock:
                    await self.db.execute("UPDATE inactivity_tracking SET user_ids = ? WHERE id = 1",
                                          (",".join(map(str, current_inactive_uids)),));
                self.previous_inactive_members = current_inactive_uids;
                logging.info(f"[Report Task] Updated inactivity tracking DB with {len(current_inactive_uids)} members.")
            except Exception:
                logging.exception("[Report Task] Failed to update inactivity tracking DB.")
        except Exception:
            logging.exception("[Report Task] An unexpected error occurred in the report loop.")

    @reportLoop.before_loop
    async def before_reportLoop(self):
        await self.wait_until_ready(); logging.info("[Report Task] Ready.")


# --- ボイスセッション処理 ---
class VoiceSess:
    @staticmethod
    def get_mute_state(vs: Optional[discord.VoiceState]) -> bool:
        return not vs or vs.mute or vs.self_mute

    @staticmethod
    async def finSess(bot: MyBot, member: Optional[discord.Member], ch_id: int, start: datetime,
                      total_duration_sec: int, user_id: Optional[int] = None) -> None:
        if total_duration_sec <= 0: return
        final_user_id = member.id if member else user_id
        if not final_user_id: logging.error(f"finSess failed: No user_id for ch {ch_id}, start {start}."); return
        end_utc = TimeMgr.now_utc();
        start_str, end_str = Util.dtStr(start), Util.dtStr(end_utc)
        table = "voice_session_logs_reward" if ch_id in REWARD_VC_CHANNELS else "voice_session_logs"
        query = f"INSERT INTO {table} (user_id, channel_id, session_start, session_end, duration) VALUES (?, ?, ?, ?, ?)"
        try:
            await DBH.execQuery(bot.db, bot.db_lock, query,
                                (final_user_id, ch_id, start_str, end_str, total_duration_sec))
            logging.info(
                f"User {final_user_id} session ended in {ch_id}. Dur: {Util.fmtDur(total_duration_sec)}. Recorded at {end_str} UTC.")
        except Exception:
            logging.exception(f"Failed to record session for {final_user_id} in {table}")

    @staticmethod
    async def handleExit(bot: MyBot, member: discord.Member, ch_id: int, now: datetime) -> None:
        user_id = member.id;
        sess_data = bot.voice_state_tracking.get(user_id)
        if sess_data and sess_data.get("channel_id") == ch_id:
            if not sess_data.get("muted", False) and sess_data.get("active_start"):
                sess_data["accumulated"] += (now - sess_data["active_start"]).total_seconds()
            await VoiceSess.finSess(bot, member, ch_id, sess_data["session_start"], int(sess_data["accumulated"]),
                                    user_id=user_id)
            bot.voice_state_tracking.pop(user_id, None);
            logging.debug(f"User {user_id} exited tracked {ch_id}. Data removed.")

    @staticmethod
    async def handleEnter(bot: MyBot, member: discord.Member, ch_id: int, now: datetime, is_muted: bool) -> None:
        user_id = member.id
        if user_id in bot.voice_state_tracking: logging.warning(
            f"User {user_id} entered {ch_id} but already tracked. Overwriting.")
        bot.voice_state_tracking[user_id] = {"channel_id": ch_id, "session_start": now,
                                             "active_start": now if not is_muted else None, "accumulated": 0.0,
                                             "muted": is_muted, "guild_id": member.guild.id}
        logging.info(f"User {user_id} joined tracked {ch_id} at {Util.dtStr(now)} UTC. Muted: {is_muted}")

    @staticmethod
    async def update_voice_sessions(bot: MyBot, member: discord.Member, before: discord.VoiceState,
                                    after: discord.VoiceState) -> None:
        now_utc = TimeMgr.now_utc();
        before_ch_id = before.channel.id if before.channel else None;
        after_ch_id = after.channel.id if after.channel else None
        if before_ch_id != after_ch_id:  # Ch change
            if before_ch_id in ALL_TRACKED_CHANNELS: await VoiceSess.handleExit(bot, member, before_ch_id, now_utc)
            if after_ch_id in ALL_TRACKED_CHANNELS: await VoiceSess.handleEnter(bot, member, after_ch_id, now_utc,
                                                                                VoiceSess.get_mute_state(after))
            if before.channel: await RoomCraftSess.updSess(bot, before.channel, now_utc)  # RC update
            if after.channel:
                await RoomCraftSess.updSess(bot, after.channel, now_utc)  # RC update
                if not before.channel and after_ch_id in ALL_TRACKED_CHANNELS:  # RC start check
                    await asyncio.sleep(0.5);
                    current_members = [m for m in after.channel.members if not m.bot]
                    if len(current_members) == 1 and current_members[0].id == member.id: await RoomCraftSess.startSess(
                        bot, member, after.channel, now_utc)
            active_rc_session = bot.room_craftsman_sessions.get(member.id)  # RC end check
            if active_rc_session and (
                    not after.channel or after_ch_id != active_rc_session["channel_id"]): await RoomCraftSess.endSess(
                bot, member.id, now_utc)
        elif after_ch_id in ALL_TRACKED_CHANNELS:  # Same Ch
            sess_data = bot.voice_state_tracking.get(member.id)  # Mute change
            if sess_data:
                prev_mute, current_mute = sess_data.get("muted", False), VoiceSess.get_mute_state(after)
                if prev_mute != current_mute:
                    if not prev_mute and current_mute:  # Muted
                        if sess_data.get("active_start"): sess_data["accumulated"] += (
                                    now_utc - sess_data["active_start"]).total_seconds()
                        sess_data.update({"active_start": None, "muted": True})
                    elif prev_mute and not current_mute:
                        sess_data.update({"active_start": now_utc, "muted": False})  # Unmuted
            if after.channel: await RoomCraftSess.updSess(bot, after.channel, now_utc)  # RC update


# --- 部屋職人セッション処理 ---
class RoomCraftSess:
    @staticmethod
    async def updSess(bot: MyBot, channel: discord.VoiceChannel, now: datetime) -> None:
        if not channel: return
        current_members = [m for m in channel.members if not m.bot];
        num_members = len(current_members);
        member_ids = {m.id for m in current_members}
        for user_id in list(bot.room_craftsman_sessions.keys()):
            sess = bot.room_craftsman_sessions.get(user_id)
            if not sess or sess["channel_id"] != channel.id or user_id not in member_ids: continue
            time_delta_sec = (now - sess["last_update"]).total_seconds()
            if time_delta_sec <= 0: continue
            if num_members > 1:  # Together
                if sess["state"] == "alone":  # alone -> together
                    sess["state"] = "together";
                    sess["max_alone"] = max(sess.get("max_alone", 0),
                                            (now - sess["alone_start"]).total_seconds() if sess.get(
                                                "alone_start") else 0);
                    sess["alone_start"] = None
                    if sess["initial_alone"] is None: sess["initial_alone"] = (
                                now - sess["session_start"]).total_seconds()
                sess["together_duration"] += time_delta_sec;
                sess["joiners"].update(member_ids - {user_id})
            elif sess["state"] == "together":
                sess["state"] = "alone"; sess["alone_start"] = now  # together -> alone
            sess["last_update"] = now

    @staticmethod
    async def startSess(bot: MyBot, member: discord.Member, channel: discord.VoiceChannel, now: datetime) -> None:
        user_id = member.id
        if user_id in bot.room_craftsman_sessions: logging.warning(f"RC session already exists for {user_id}."); return
        non_bot_members = [m for m in channel.members if not m.bot]
        if len(non_bot_members) == 1 and non_bot_members[0].id == user_id:
            bot.room_craftsman_sessions[user_id] = {"user_id": user_id, "channel_id": channel.id, "session_start": now,
                                                    "last_update": now, "state": "alone", "alone_start": now,
                                                    "initial_alone": None, "together_duration": 0.0, "joiners": set(),
                                                    "max_alone": 0.0, "guild_id": member.guild.id}
            logging.info(f"Started RC session for user {user_id} in {channel.id}.")

    @staticmethod
    async def endSess(bot: MyBot, user_id: int, now: datetime) -> None:
        sess = bot.room_craftsman_sessions.pop(user_id, None)
        if not sess: return
        sess_end_time = now;
        time_delta_sec = (sess_end_time - sess["last_update"]).total_seconds()
        if time_delta_sec > 0:  # Final update
            if sess["state"] == "together":
                sess["together_duration"] += time_delta_sec
            elif sess["state"] == "alone" and sess.get("alone_start"):
                sess["max_alone"] = max(sess.get("max_alone", 0), (sess_end_time - sess["alone_start"]).total_seconds())
        if sess["initial_alone"] is None: sess["initial_alone"] = (
                    sess_end_time - sess["session_start"]).total_seconds()
        logging.info(
            f"Ending RC session for {user_id}. Joiners: {len(sess['joiners'])}, Together: {Util.fmtDur(int(sess['together_duration']))}, Max Alone: {Util.fmtDur(int(sess['max_alone']))}")
        if sess["joiners"] and sess.get("max_alone", 0) < 1800:  # Check criteria
            score = int((sess["together_duration"] / 60) * len(sess["joiners"]))
            if score > 0:
                start_str, end_str = Util.dtStr(sess["session_start"]), Util.dtStr(sess_end_time)
                query = "INSERT INTO room_craftsman_sessions (user_id, channel_id, session_start, session_end, together_duration, join_count, score) VALUES (?, ?, ?, ?, ?, ?, ?)"
                params = (sess["user_id"], sess["channel_id"], start_str, end_str, int(sess["together_duration"]),
                          len(sess["joiners"]), score)
                try:
                    await DBH.execQuery(bot.db, bot.db_lock, query, params); logging.info(
                        f"Recorded RC session for {user_id}. Score: {score}")
                except Exception:
                    logging.exception(f"Failed to record RC session for {user_id}")
            else:
                logging.info(f"RC session for {user_id} ended but score was 0.")
        else:
            reason = "no joiners" if not sess[
                "joiners"] else f"max_alone>=1800s ({sess.get('max_alone', 0):.0f}s)"; logging.info(
                f"RC session for {user_id} ended but not recorded ({reason}).")

    @staticmethod
    async def handleVSU(bot: MyBot, member: discord.Member, before: discord.VoiceState,
                        after: discord.VoiceState) -> None:
        pass


# --- 表彰計算 ---
class AwardCalc:
    # --------------------------------------------------
    # 埋め込み生成ユーティリティ
    # --------------------------------------------------
    @classmethod
    def mkAwardEmbed(
            cls,
            awards: Dict[str, Any],
            year: int,
            month: int,
            hist: Dict[str, Any],
            admin_view: bool = False,
    ) -> discord.Embed:
        """
        男女混合 1 枚でまとめて出す簡易版。（publish 用で採用）
        """
        embed = discord.Embed(
            title=f"{year}年{month}月度 【男女別】 表彰リスト",
            color=0x1E90FF,
            timestamp=TimeMgr.now_jst(),
        )
        embed.set_footer(text="BOT自動集計")

        # (キー, 表示名, 時間扱いか, 単位)
        fields_def = [
            ("longest_call", ":trophy: **最長通話賞**", True, ""),
            ("longest_session", ":repeat: **長時間通話賞**", True, ""),
            ("most_parts", ":busts_in_silhouette: **最多人数賞**", False, "人"),
            ("most_sessions", ":bar_chart: **浮上回数賞**", False, "回"),
            ("level_up", ":chart_with_upwards_trend: **レベルアップ賞**", True, ""),
            ("weekend_award", ":calendar: **週末賞**", True, ""),
            ("newcomer", ":baby: **新人賞**", False, "人"),
            ("welcome", ":wave: **ウェルカム賞**", False, "人"),
            ("morning_activity", ":sunrise: **朝活賞**", True, ""),
            ("afternoon_activity", ":sunny: **昼活賞**", True, ""),
            ("evening_activity", ":city_sunset: **夕活賞**", True, ""),
            ("night_activity", ":night_with_stars: **夜活賞**", True, ""),
            ("late_night_activity", ":sleeping: **夜更かし賞**", True, ""),
            ("room_craftsman", ":house_with_garden: **部屋職人賞**", False, "点"),
        ]
        allowed_details = {"longest_session", "most_parts", "newcomer", "welcome"}

        def strip_parentheses(txt: str) -> str:
            return re.sub(r"\s*\(.*?\)", "", txt)

        for key, name, is_time, suffix in fields_def:
            data = awards.get(key)
            if not data:
                continue
            if key == "newcomer":
                m_val = Util.listOrNone(f"<@{uid}>" for uid in data.get("male", []))
                f_val = Util.listOrNone(f"<@{uid}>" for uid in data.get("female", []))
            else:
                m_val = cls.fmt_line_top3(data.get("male", [])[:3], is_time, suffix)
                f_val = cls.fmt_line_top3(data.get("female", [])[:3], is_time, suffix)
                if not admin_view and key not in allowed_details:
                    m_val = strip_parentheses(m_val)
                    f_val = strip_parentheses(f_val)
            field_text = f"男性: {m_val}\n女性: {f_val}"
            # 分割して 1024 字制限に対応
            for i, chunk in enumerate(Util.splitEmbed(field_text)):
                embed.add_field(
                    name=f"{name}{f' (Part {i + 1})' if i else ''}",
                    value=chunk,
                    inline=False,
                )

        # 皆勤賞は別処理
        perf = awards.get("perfect_attendance", {"male": [], "female": []})
        m_perf = Util.listOrNone(f"<@{uid}>" for uid in perf.get("male", []))
        f_perf = Util.listOrNone(f"<@{uid}>" for uid in perf.get("female", []))
        perf_text = f"男性: {m_perf}\n女性: {f_perf}"
        for i, chunk in enumerate(Util.splitEmbed(perf_text)):
            embed.add_field(
                name=f":sparkles: **皆勤賞**{f' (Part {i + 1})' if i else ''}",
                value=chunk,
                inline=False,
            )
        return embed

    @classmethod
    def mkAwardEmbeds(
            cls,
            awards: Dict[str, Any],
            year: int,
            month: int,
            hist: Dict[str, Any],
            admin_view: bool = False,
    ) -> Tuple[discord.Embed, discord.Embed]:
        """
        男性用＋女性用の 2 枚セットを返すフル版。（adm_current_awards などで使用）
        """
        em_male = discord.Embed(
            title=f"{year}年{month}月度 【男性】 表彰リスト",
            color=0x1E90FF,
            timestamp=TimeMgr.now_jst(),
        )
        em_fem = discord.Embed(
            title=f"{year}年{month}月度 【女性】 表彰リスト",
            color=0xFFC0CB,
            timestamp=TimeMgr.now_jst(),
        )
        em_male.set_footer(text="BOT自動集計")
        em_fem.set_footer(text="BOT自動集計")

        fields_def = [
            ("longest_call", ":trophy: **最長通話賞**", True, ""),
            ("longest_session", ":repeat: **長時間通話賞**", True, ""),
            ("most_parts", ":busts_in_silhouette: **最多人数賞**", False, "人"),
            ("most_sessions", ":bar_chart: **浮上回数賞**", False, "回"),
            ("level_up", ":chart_with_upwards_trend: **レベルアップ賞**", True, ""),
            ("weekend_award", ":calendar: **週末賞**", True, ""),
            ("newcomer", ":baby: **新人賞**", False, "人"),
            ("welcome", ":wave: **ウェルカム賞**", False, "人"),
            ("morning_activity", ":sunrise: **朝活賞**", True, ""),
            ("afternoon_activity", ":sunny: **昼活賞**", True, ""),
            ("evening_activity", ":city_sunset: **夕活賞**", True, ""),
            ("night_activity", ":night_with_stars: **夜活賞**", True, ""),
            ("late_night_activity", ":sleeping: **夜更かし賞**", True, ""),
            ("room_craftsman", ":house_with_garden: **部屋職人賞**", False, "点"),
        ]
        allowed_details = {"longest_session", "most_parts", "newcomer", "welcome"}

        for key, name, is_time, suffix in fields_def:
            data = awards.get(key)
            if not data:
                continue
            if key == "newcomer":
                m_val = Util.listOrNone(f"<@{uid}>" for uid in data.get("male", []))
                f_val = Util.listOrNone(f"<@{uid}>" for uid in data.get("female", []))
            else:
                m_val = cls.fmt_line_top3(data.get("male", [])[:3], is_time, suffix)
                f_val = cls.fmt_line_top3(data.get("female", [])[:3], is_time, suffix)
                if not admin_view and key not in allowed_details:
                    m_val = re.sub(r"\s*\(.*?\)", "", m_val)
                    f_val = re.sub(r"\s*\(.*?\)", "", f_val)
            for i, chunk in enumerate(Util.splitEmbed(m_val)):
                em_male.add_field(
                    name=f"{name}{f' (Part {i + 1})' if i else ''}",
                    value=chunk,
                    inline=False,
                )
            for i, chunk in enumerate(Util.splitEmbed(f_val)):
                em_fem.add_field(
                    name=f"{name}{f' (Part {i + 1})' if i else ''}",
                    value=chunk,
                    inline=False,
                )

        # 皆勤賞
        perf = awards.get("perfect_attendance", {"male": [], "female": []})
        m_perf = Util.listOrNone(f"<@{uid}>" for uid in perf.get("male", []))
        f_perf = Util.listOrNone(f"<@{uid}>" for uid in perf.get("female", []))
        for i, chunk in enumerate(Util.splitEmbed(m_perf)):
            em_male.add_field(
                name=f":sparkles: **皆勤賞**{f' (Part {i + 1})' if i else ''}",
                value=chunk,
                inline=False,
            )
        for i, chunk in enumerate(Util.splitEmbed(f_perf)):
            em_fem.add_field(
                name=f":sparkles: **皆勤賞**{f' (Part {i + 1})' if i else ''}",
                value=chunk,
                inline=False,
            )
        return em_male, em_fem

    # --------------------------------------------------
    # 共通ユーティリティ
    # --------------------------------------------------
    @staticmethod
    def awardEntTop3() -> List[Dict[str, Any]]:
        return []

    @staticmethod
    def upd_award_top3(ranking: list, uid: int, new_val: float) -> None:
        if new_val <= 0:
            return
        # スコアが既にある場合はユーザーを追加
        for entry in ranking:
            if entry["value"] == new_val:
                if uid not in entry["users"]:
                    entry["users"].append(uid)
                return
        # 新しいスコアが高ければ挿入（降順）
        inserted = False
        for i, entry in enumerate(ranking):
            if new_val > entry["value"]:
                ranking.insert(i, {"value": new_val, "users": [uid]})
                inserted = True
                break
        if not inserted and len(ranking) < 3:
            ranking.append({"value": new_val, "users": [uid]})
        # 上位 3 に収める
        if len(ranking) > 3:
            ranking.pop()

    @staticmethod
    def fmt_line_top3(ranking: list, is_time: bool, suffix: str) -> str:
        if not ranking:
            return "該当者なし"
        pos = ["1位", "2位", "3位"]
        lines = []
        for i, entry in enumerate(ranking):
            users = ", ".join(f"<@{uid}>" for uid in entry["users"])
            val = Util.fmtDur(int(entry["value"])) if is_time else f"{int(round(entry['value']))}{suffix}"
            lines.append(f"{pos[i]}: {users} ({val})")
        return "\n".join(lines)

    @staticmethod
    def calcMA_sec(s_jst: datetime, e_jst: datetime) -> Tuple[int, int]:
        morn = aftr = 0
        cur = s_jst
        while cur < e_jst:
            h = cur.hour
            if 6 <= h < 10:
                end_h = 10
            elif 10 <= h < 15:
                end_h = 15
            else:
                next_h = 6 if h >= 15 else 6 if h < 6 else 10 if h < 10 else 15
                next_day = cur + timedelta(days=1) if h >= 15 or next_h <= h else cur
                cur = next_day.replace(hour=next_h, minute=0, second=0, microsecond=0)
                continue
            block_end = min(cur.replace(hour=end_h, minute=0, second=0, microsecond=0), e_jst)
            dur = (block_end - cur).total_seconds()
            (morn if h < 10 else aftr).__iadd__(dur)  # type: ignore
            cur = block_end
        return int(morn), int(aftr)

    # --------------------------------------------------
    # 月次表彰メイン
    # --------------------------------------------------
    @staticmethod
    async def calcMonthly(
            bot: "MyBot",
            year: int,
            month: int,
            guild: discord.Guild,
            *,
            until: Optional[datetime] = None,
    ) -> Dict[str, Any]:

        JST, UTC = TimeMgr.JST, TimeMgr.UTC
        start_jst = datetime(year, month, 1, tzinfo=JST)
        next_y, next_m = (year + 1, 1) if month == 12 else (year, month + 1)
        end_jst = datetime(next_y, next_m, 1, tzinfo=JST)
        start_utc = start_jst.astimezone(UTC)
        end_utc = end_jst.astimezone(UTC)

        # ―― 前月期間 ――
        prev_y, prev_m = (year - 1, 12) if month == 1 else (year, month - 1)
        prev_start_jst = datetime(prev_y, prev_m, 1, tzinfo=JST)
        prev_start_utc = prev_start_jst.astimezone(UTC)
        prev_end_jst = start_jst
        prev_end_utc = prev_end_jst.astimezone(UTC)

        # ------------- 除外ユーザー -------------
        async with bot.db_lock:
            excl_rows = await DBH.fetchAll(
                bot.db,
                "SELECT user_id FROM reward_exclusions WHERE guild_id = ?",
                (guild.id,),
            )
        exclusions = {r["user_id"] for r in excl_rows}

        # ------------- 対象セッション取得 -------------
        async with bot.db_lock:
            cur_rows = await DBH.fetchAll(
                bot.db,
                """
                SELECT user_id, channel_id, session_start, session_end, duration
                FROM voice_session_logs_reward
                WHERE session_end > ?
                  AND session_start < ?
                """,
                (Util.dtStr(start_utc), Util.dtStr(end_utc)),
            )
            prev_rows = await DBH.fetchAll(
                bot.db,
                """
                SELECT user_id, session_start, session_end, duration
                FROM voice_session_logs_reward
                WHERE session_end > ?
                  AND session_start < ?
                """,
                (Util.dtStr(prev_start_utc), Util.dtStr(prev_end_utc)),
            )

        # ---------- 途中経過締切日判定 ----------
        if until:
            last_day_date = (until.astimezone(JST).date() - timedelta(days=1))
        else:
            last_day_date = TimeMgr.now_jst().date() - timedelta(days=1)
        month_end_date = (end_jst - timedelta(seconds=1)).date()
        last_day_date = min(last_day_date, month_end_date)

        if last_day_date < start_jst.date():
            all_days: set[str] = set()
        else:
            total_days = (last_day_date - start_jst.date()).days + 1
            all_days = {
                (start_jst + timedelta(days=i)).strftime("%Y-%m-%d")
                for i in range(total_days)
            }

        # ---------- マップ初期化 ----------
        tot_dur, prev_tot_dur = defaultdict(float), defaultdict(float)
        max_one, sess_cnt = defaultdict(float), defaultdict(int)
        wkend_dur = defaultdict(float)
        morn_dur, aft_dur, eve_dur, night_dur, late_dur = (defaultdict(float) for _ in range(5))

        weekend_periods = Util.getWkendPeriods(start_jst, end_jst)

        # ---------- 共通行処理 ----------
        def _process_row(
                r: aiosqlite.Row,
                tgt: Dict[int, float],
                clip_s: datetime,
                clip_e: datetime,
        ) -> Optional[Tuple[int, datetime, datetime, float]]:
            uid = r["user_id"]
            if uid in exclusions:
                return None
            st = Util.parseUTC(r["session_start"]).astimezone(JST)
            ed = Util.parseUTC(r["session_end"]).astimezone(JST)
            st, ed = max(st, clip_s), min(ed, clip_e)
            if ed <= st:
                return None
            dur_full = max(
                (Util.parseUTC(r["session_end"]) - Util.parseUTC(r["session_start"])).total_seconds(),
                0.0,
            )
            if dur_full == 0:
                return None
            eff = float(r["duration"] or 0) * ((ed - st).total_seconds() / dur_full)
            if eff <= 0:
                return None
            tgt[uid] += eff
            return uid, st, ed, eff

        # ---------- 今月 ----------
        for r in cur_rows:
            res = _process_row(r, tot_dur, start_jst, end_jst)
            if not res:
                continue
            uid, st, ed, eff = res
            max_one[uid] = max(max_one[uid], eff)
            sess_cnt[uid] += 1
            for ps, pe in weekend_periods:
                ov = min(ed, pe) - max(st, ps)
                if ov.total_seconds() > 0:
                    wkend_dur[uid] += ov.total_seconds()
            cur = st
            while cur < ed:
                nxt = min(ed, cur.replace(minute=0, second=0, microsecond=0) + timedelta(hours=1))
                h, sec = cur.hour, (nxt - cur).total_seconds()
                if 6 <= h < 10:
                    morn_dur[uid] += sec
                elif 10 <= h < 15:
                    aft_dur[uid] += sec
                elif 15 <= h < 19:
                    eve_dur[uid] += sec
                elif 19 <= h < 24:
                    night_dur[uid] += sec
                else:
                    late_dur[uid] += sec
                cur = nxt

        # ---------- 前月 (レベルアップ賞の比較用のみ) ----------
        for r in prev_rows:
            _process_row(r, prev_tot_dur, prev_start_jst, start_jst)

        # ========== 新人賞・ウェルカム賞 ==========
        async with bot.db_lock:
            n_rows = await DBH.fetchAll(
                bot.db,
                "SELECT user_id, submitted_at FROM profile_submission_log WHERE submitted_at >= ? AND submitted_at < ?",
                (Util.dtStr(start_utc - timedelta(days=14)), Util.dtStr(end_utc)),
            )
        newcomer_window: dict[int, Tuple[datetime, datetime]] = {}
        for row in n_rows:
            uid, sub_dt = row["user_id"], Util.parseUTC(row["submitted_at"])
            w_end = sub_dt + timedelta(days=14)
            if start_utc <= w_end < end_utc:
                member = guild.get_member(uid)
                if member and any(r.id == NEWCOMER_ROLE_ID for r in member.roles):
                    newcomer_window[uid] = (sub_dt, w_end)
        async with bot.db_lock:
            sess_rows = await DBH.fetchAll(
                bot.db,
                "SELECT user_id, channel_id, session_start, session_end FROM voice_session_logs_reward WHERE session_end > ? AND session_start < ?",
                (Util.dtStr(start_utc - timedelta(days=14)), Util.dtStr(end_utc)),
            )
        ch_map: dict[int, list[Tuple[int, datetime, datetime]]] = defaultdict(list)
        for r in sess_rows:
            ch_map[r["channel_id"]].append(
                (r["user_id"], Util.parseUTC(r["session_start"]), Util.parseUTC(r["session_end"])))
        dur_sec: dict[int, float] = defaultdict(float)
        partners: dict[int, set[int]] = defaultdict(set)
        for uid, (w_st, w_ed) in newcomer_window.items():
            for ch_id, lst in ch_map.items():
                tgt_sess = [(st, ed) for u, st, ed in lst if u == uid and ed > w_st and st < w_ed]
                if not tgt_sess: continue
                for st, ed in tgt_sess:
                    dur_sec[uid] += ovlp_sec(st, ed, w_st, w_ed)
                for st1, ed1 in tgt_sess:
                    for u2, st2, ed2 in lst:
                        if u2 == uid or u2 in exclusions: continue
                        if ovlp_sec(st1, ed1, st2, ed2) >= 1 and st2 < w_ed and ed2 > w_st:
                            partners[uid].add(u2)
        WEIGHT_DUR, WEIGHT_PARTNER = 0.6, 0.4
        newcomer_score: dict[int, float] = {
            uid: (dur_sec[uid] / 3600.0) * WEIGHT_DUR + len(partners[uid]) * WEIGHT_PARTNER for uid in newcomer_window
            if dur_sec[uid] > 0}

        def _top3_id(src: dict[int, float], gender: str) -> list[int]:
            lst = [(uid, v) for uid, v in src.items() if getSex(guild.get_member(uid)) == gender]
            if not lst: return []
            lst.sort(key=lambda t: t[1], reverse=True)
            top3 = lst[:3]
            if len(lst) > 3 and lst[3][1] == top3[-1][1]:
                last_val = top3[-1][1]
                top3.extend([p for p in lst[3:] if p[1] == last_val])
            return [uid for uid, _ in top3]

        newcomer_male, newcomer_female = _top3_id(newcomer_score, "male"), _top3_id(newcomer_score, "female")
        newcomer_set = set(newcomer_window)
        wel_counter: dict[int, set[int]] = defaultdict(set)
        for ch_id, lst in ch_map.items():
            for i in range(len(lst)):
                u1, s1, e1 = lst[i]
                for j in range(i + 1, len(lst)):
                    u2, s2, e2 = lst[j]
                    if u1 == u2 or (u1 not in newcomer_set and u2 not in newcomer_set): continue
                    if ovlp_sec(s1, e1, s2, e2) < 1: continue
                    if u1 in newcomer_set and u2 not in newcomer_set:
                        wel_counter[u2].add(u1)
                    elif u2 in newcomer_set and u1 not in newcomer_set:
                        wel_counter[u1].add(u2)
        welcome_score = {uid: len(s) for uid, s in wel_counter.items() if s}

        # ========== レベルアップ賞 ==========
        prev2_end_utc = ((start_jst.replace(day=1) - timedelta(seconds=1)).replace(tzinfo=JST)).astimezone(UTC)
        async with bot.db_lock:
            rows = await DBH.fetchAll(bot.db, "SELECT user_id FROM profile_submission_log WHERE submitted_at <= ?",
                                      (Util.dtStr(prev2_end_utc),))
        eligible_lv = {r["user_id"] for r in rows}
        lvup_map = {uid: tot_dur[uid] - prev_tot_dur.get(uid, 0.0) for uid in tot_dur if
                    uid in eligible_lv and (tot_dur[uid] - prev_tot_dur.get(uid, 0.0)) > 0}

        # ---------- Top3 ヘルパ ----------
        def _top3(src: Dict[int, float]) -> Dict[str, list]:
            """Return top 3 users per gender, limiting ties to at most 3 names."""
            res = {"male": [], "female": []}
            gender_map = {"male": [], "female": []}
            for uid, v in src.items():
                sex = getSex(guild.get_member(uid))
                if sex in ("male", "female"):
                    gender_map[sex].append((uid, v))

            for sex, lst in gender_map.items():
                lst.sort(key=lambda t: (-t[1], t[0]))
                user_count = 0
                for uid, val in lst:
                    if user_count >= 3:
                        break
                    if res[sex] and res[sex][-1]["value"] == val:
                        res[sex][-1]["users"].append(uid)
                    else:
                        if len(res[sex]) == 3:
                            break
                        res[sex].append({"value": val, "users": [uid]})
                    user_count += 1

            return res

        # ========== 皆勤賞 ==========
        user_day_sec: Dict[int, Dict[str, float]] = defaultdict(lambda: defaultdict(float))
        for r in cur_rows:
            uid, st, ed = r["user_id"], Util.parseUTC(r["session_start"]).astimezone(JST), Util.parseUTC(
                r["session_end"]).astimezone(JST)
            for key, seg_s, seg_e in Util.splitSessDay(st, ed):
                if key in all_days:
                    user_day_sec[uid][key] += (seg_e - seg_s).total_seconds()

        def _perfect(gender: str) -> list[int]:
            lst: list[int] = []
            for uid, day_map in user_day_sec.items():
                mem = guild.get_member(uid)
                if not mem: continue
                rids = {r.id for r in mem.roles}
                sex = getSex(mem)
                if gender == "male":
                    eligible = (sex == "male") or (EXTRA_ATTEND_MALE_ROLE_ID in rids)
                elif gender == "female":
                    eligible = (sex == "female") or (EXTRA_ATTEND_FEMALE_ROLE_ID in rids)
                else:
                    eligible = False
                if not eligible: continue
                if all(day_map.get(d, 0.0) >= 180 for d in all_days):
                    lst.append(uid)
            return lst

        # ========== Room Craftsman ==========
        rc_rows = await DBH.fetchAll(bot.db,
                                     "SELECT user_id, SUM(score) AS sc FROM room_craftsman_sessions WHERE session_end > ? AND session_start < ? GROUP BY user_id",
                                     (Util.dtStr(start_utc), Util.dtStr(end_utc)))

        # ========== awards dict ==========
        awards = {
            "longest_call": _top3(tot_dur),
            "longest_session": _top3(max_one),
            "most_sessions": _top3(sess_cnt),
            "weekend_award": _top3(wkend_dur),
            "morning_activity": _top3(morn_dur),
            "afternoon_activity": _top3(aft_dur),
            "evening_activity": _top3(eve_dur),
            "night_activity": _top3(night_dur),
            "late_night_activity": _top3(late_dur),
            "room_craftsman": _top3({r["user_id"]: r["sc"] for r in rc_rows}),
            "newcomer": {"male": newcomer_male, "female": newcomer_female},
            "level_up": _top3(lvup_map),
            "welcome": _top3(welcome_score),
            "perfect_attendance": {"male": _perfect("male"), "female": _perfect("female")},
        }

        if os.getenv("AWARD_DEBUG", "0") == "1":
            dbg = [f"[皆勤デバッグ] {year}-{month}"]
            for g in ("male", "female"):
                cand = _perfect(g)
                dbg.append(f"{g.upper()}: {len(cand)} 人 -> {', '.join(map(str, cand)) or 'なし'}")
            logging.debug("\n".join(dbg))

        return awards
    # --------------------------------------------------
    # 履歴関連（getAwardHist / saveMonthlyHist など）
    # --------------------------------------------------
    @classmethod
    async def getAwardHist(cls, bot: MyBot, guild: discord.Guild) -> Dict[str, Any]:
        hist: Dict[str, Any] = {}
        if not bot.db:
            return hist
        try:
            async with bot.db_lock:
                rows = await DBH.fetchAll(
                    bot.db,
                    "SELECT award_name, user_id, value FROM monthly_award_history WHERE guild_id = ?",
                    (guild.id,),
                )
            for row in rows:
                award, uid, val = row["award_name"], row["user_id"], row["value"]
                if award not in hist:
                    hist[award] = {
                        "male": defaultdict(int),
                        "female": defaultdict(int),
                        "max_male": 0.0,
                        "max_female": 0.0,
                    }
                mem = guild.get_member(uid)
                s = getSex(mem)
                if s in ("male", "female"):
                    hist[award][s][uid] += 1
                    if award != "皆勤賞":
                        key = f"max_{s}"
                        hist[award][key] = max(hist[award][key], val or 0.0)
        except Exception:
            logging.exception("Failed to get award history.")
        return hist

    # --------------------------------------------------
    # 月次履歴保存
    # --------------------------------------------------
    @classmethod
    async def saveMonthlyHist(
            cls,
            bot: "MyBot",
            awards: Dict[str, Any],
            guild_id: int,
            year: int,
            month: int,
    ) -> None:
        """
        monthly_award_history テーブルへ **その月の確定結果** を保存する。
        - 既存レコードがあれば上書き（DELETE → INSERT）
        - 数値系は value をそのまま保存
        - リスト系（新人賞・皆勤賞など）は value=0
        """
        if not bot.db:
            return

        async with bot.db_lock:
            # いったんその月の既存分を削除
            await bot.db.execute(
                "DELETE FROM monthly_award_history WHERE guild_id=? AND year=? AND month=?",
                (guild_id, year, month),
            )

            insert_q = """
                       INSERT INTO monthly_award_history
                           (guild_id, year, month, award_name, user_id, value)
                       VALUES (?, ?, ?, ?, ?, ?) \
                       """

            # --- 各賞ごとに保存 --------------------------------------
            for award_name, data in awards.items():
                # 数値ランキング系
                if isinstance(data.get("male"), list) and data.get("male") and isinstance(data["male"][0], dict):
                    # entry = {"value": xxx, "users": [id, ...]}
                    for gender in ("male", "female"):
                        for entry in data.get(gender, []):
                            val = entry["value"]
                            for uid in entry["users"]:
                                await bot.db.execute(
                                    insert_q,
                                    (guild_id, year, month, award_name, uid, float(val)),
                                )
                # ユーザーIDだけのリスト系（新人賞・皆勤賞など）
                else:
                    for gender in ("male", "female"):
                        for uid in data.get(gender, []):
                            await bot.db.execute(
                                insert_q,
                                (guild_id, year, month, award_name, uid, 0.0),
                            )

            await bot.db.commit()
            logging.info(f"Saved monthly history for {year}-{month} ({guild_id}).")


# --- 管理者チェック ---
def isAdmin() -> Any:
    async def predicate(interaction: discord.Interaction) -> bool:
        if not isinstance(interaction.user, discord.Member): await interaction.response.send_message(
            "サーバー内でのみ使用できます。", ephemeral=True); return False
        if interaction.user.guild_permissions.administrator or any(
            r.id in EXTRA_ADMIN_ROLES for r in interaction.user.roles): return True
        await interaction.response.send_message("このコマンドを実行する権限がありません。", ephemeral=True);
        return False

    return app_commands.check(predicate)


# --- スラッシュコマンド Cog ---
class RewardCmd(commands.Cog):
    def __init__(self, bot: MyBot) -> None:
        self.bot = bot

    @app_commands.command(name="adm_remove_profile_submission")
    @isAdmin()
    async def adm_remove_profile_submission(
            self,
            interaction: discord.Interaction,
            member: discord.Member,
    ) -> None:
        """指定メンバーの profile_submission_log を削除"""
        await interaction.response.defer(ephemeral=True)
        async with self.bot.db_lock:
            await self.bot.db.execute(
                "DELETE FROM profile_submission_log WHERE user_id = ?",
                (member.id,),
            )
        await interaction.followup.send(
            f"✅ {member.mention} のプロフィール提出レコードを削除しました。",
            ephemeral=True,
        )

    # --- 皆勤補填コマンド --------------------------------------------------
    @app_commands.command(name="adm_add_attendance")
    @isAdmin()
    async def admAddAttendanceCmd(
            self,
            interaction: discord.Interaction,
            date_jst: str,
            member: Optional[discord.Member] = None,
            duration_sec: Optional[int] = 180,
    ) -> None:
        """
        指定日に“通話 180 秒”に満たない場合のみ補填する管理者コマンド。
        member を指定しない場合、対象ロールを持つ全メンバーを補填します。

        Parameters
        ----------
        date_jst : str
            対象日 (YYYY-MM-DD, JST)
        member : discord.Member | None, default None
            対象ユーザー。None の場合は全員対象
        duration_sec : int | None, default 180
            追加する通話秒数。None なら「不足分ぴったり」を自動計算
        """
        await interaction.response.defer(ephemeral=True)

        guild = interaction.guild
        if not guild or not self.bot.db:
            await interaction.followup.send("コマンドを利用できません。", ephemeral=True)
            return

        # ---------- 入力チェック ----------
        try:
            tgt_date = datetime.strptime(date_jst, "%Y-%m-%d").date()
        except ValueError:
            await interaction.followup.send("日付の形式が正しくありません (YYYY-MM-DD)。", ephemeral=True)
            return

        if duration_sec is not None and duration_sec < 1:
            await interaction.followup.send("duration_sec は 1 以上の整数で指定してください。", ephemeral=True)
            return

        # ---------- 期間定義 ----------
        start_jst = datetime.combine(tgt_date, time(0, 0), tzinfo=TimeMgr.JST)
        end_jst = start_jst + timedelta(days=1)
        start_utc = start_jst.astimezone(TimeMgr.UTC)
        end_utc = end_jst.astimezone(TimeMgr.UTC)

        # ---------- 対象メンバー取得 ----------
        if member is not None:
            target_members = [member]
        else:
            role_ids = set(
                MALE_ROLES
                + FEMALE_ROLES
                + [EXTRA_ATTEND_MALE_ROLE_ID, EXTRA_ATTEND_FEMALE_ROLE_ID]
            )
            target_members = [
                m
                for m in guild.members
                if (not m.bot) and any(r.id in role_ids for r in m.roles)
            ]

        # ---------- ダミーセッションを挿入 ----------
        if REWARD_VC_CHANNELS:
            channel_id = REWARD_VC_CHANNELS[0]
        elif TARGET_VC_CHANNELS:
            channel_id = TARGET_VC_CHANNELS[0]
        else:
            await interaction.followup.send("トラッキング対象 VC が設定されていません。", ephemeral=True)
            return

        success = 0
        for mem in target_members:
            async with self.bot.db_lock:
                rows = await DBH.fetchAll(
                    self.bot.db,
                    """
                    SELECT session_start, session_end
                    FROM voice_session_logs_reward
                    WHERE user_id = ?
                      AND session_end > ?
                      AND session_start < ?
                    """,
                    (mem.id, Util.dtStr(start_utc), Util.dtStr(end_utc)),
                )

            existed_sec = 0.0
            for r in rows:
                st = Util.parseUTC(r["session_start"]).astimezone(TimeMgr.JST)
                ed = Util.parseUTC(r["session_end"]).astimezone(TimeMgr.JST)
                existed_sec += max(
                    0.0,
                    (min(ed, end_jst) - max(st, start_jst)).total_seconds(),
                )

            if existed_sec >= 180:
                continue

            need_sec = 180 - int(existed_sec)
            insert_sec = need_sec if duration_sec is None else max(duration_sec, need_sec)

            sess_start_jst = datetime.combine(tgt_date, time(12, 0), tzinfo=TimeMgr.JST)
            sess_end_jst = sess_start_jst + timedelta(seconds=insert_sec)
            sess_start_utc = sess_start_jst.astimezone(TimeMgr.UTC)
            sess_end_utc = sess_end_jst.astimezone(TimeMgr.UTC)

            try:
                await DBH.execQuery(
                    self.bot.db,
                    self.bot.db_lock,
                    """
                    INSERT INTO voice_session_logs_reward
                        (user_id, channel_id, session_start, session_end, duration)
                    VALUES (?, ?, ?, ?, ?)
                    """,
                    (
                        mem.id,
                        channel_id,
                        Util.dtStr(sess_start_utc),
                        Util.dtStr(sess_end_utc),
                        insert_sec,
                    ),
                )
                logging.info(
                    f"[adm_add_attendance] uid={mem.id} {tgt_date=} existing={int(existed_sec)}s + {insert_sec}s"
                )
                success += 1
            except Exception:
                logging.exception("Failed to insert dummy attendance session.")

        if success == 0:
            await interaction.followup.send("補填対象がありません。", ephemeral=True)
        else:
            if member is not None:
                await interaction.followup.send(
                    f"✅ {member.mention} の {tgt_date} を {insert_sec} 秒分補填しました",
                    ephemeral=True,
                )
            else:
                await interaction.followup.send(
                    f"✅ {tgt_date} を {success} 名分補填しました。",
                    ephemeral=True,
                )

    # --- 皆勤賞デバッグコマンド (当月 / 前月対応版) -----------------------
    @app_commands.command(name="adm_check_attendance")
    @isAdmin()
    async def admCheckAttendanceCmd(
            self,
            interaction: discord.Interaction,
            members: Optional[str] = None,
            previous_month: bool = False,  # ★ 新オプション
    ) -> None:
        """
        ・指定ユーザーの皆勤状況をチェック
        ・previous_month が **True** のときは「前月」を対象にする
          （省略時は従来どおり当月を対象、未来日は判定対象外）
        """
        await interaction.response.defer(ephemeral=True)

        guild = interaction.guild
        if not guild or not self.bot.db:
            await interaction.followup.send("DB 未接続のため利用不可。", ephemeral=True)
            return

        # ---------- 対象ユーザー ----------
        if members:
            mids = re.findall(r"<@!?(\d+)>", members)
            target_uids = {int(m) for m in mids if m.isdigit()}
            if not target_uids:
                await interaction.followup.send("メンバーをメンションで指定してください。", ephemeral=True)
                return
        else:
            role_ids = set(MALE_ROLES + FEMALE_ROLES)
            target_uids = {
                m.id for m in guild.members
                if any(r.id in role_ids for r in m.roles)
            }

        # ---------- 期間算出 ----------
        now_jst = TimeMgr.now_jst()

        if previous_month:
            # ---- 前月 ----
            prev_year = now_jst.year if now_jst.month > 1 else now_jst.year - 1
            prev_month = now_jst.month - 1 if now_jst.month > 1 else 12
            start_jst = datetime(prev_year, prev_month, 1, tzinfo=TimeMgr.JST)

            # 前月末日を求める
            next_month_first = start_jst + timedelta(days=32)
            next_month_first = next_month_first.replace(day=1)
            last_day_date = (next_month_first - timedelta(days=1)).date()
        else:
            # ---- 当月 (未来日ノーカット) ----
            start_jst = datetime(now_jst.year, now_jst.month, 1, tzinfo=TimeMgr.JST)
            last_day_date = now_jst.date() - timedelta(days=1)  # 昨日まで
            if last_day_date < start_jst.date():  # 月頭早朝など
                last_day_date = start_jst.date() - timedelta(days=1)  # → all_days が空に

        # 1 日も対象が無ければ空 set に
        if last_day_date < start_jst.date():
            all_days: list[str] = []
        else:
            total_days = (last_day_date - start_jst.date()).days + 1
            all_days = [
                (start_jst + timedelta(days=i)).strftime("%Y-%m-%d")
                for i in range(total_days)
            ]

        # ---------- セッション取得 ----------
        end_utc = (
            datetime.combine(last_day_date + timedelta(days=1), time(0, 0),
                             tzinfo=TimeMgr.JST)
            .astimezone(TimeMgr.UTC)
        )

        async with self.bot.db_lock:
            rows = await DBH.fetchAll(
                self.bot.db,
                f"""
                SELECT user_id, session_start, session_end
                  FROM voice_session_logs_reward
                 WHERE session_end   > ?
                   AND session_start < ?
                   AND user_id IN ({','.join('?' * len(target_uids))})
                """,
                (
                    Util.dtStr(start_jst.astimezone(TimeMgr.UTC)),
                    Util.dtStr(end_utc),
                    *target_uids,
                ),
            )

        # ---------- 秒数集計 ----------
        user_day_sec: Dict[int, Dict[str, float]] = defaultdict(
            lambda: defaultdict(float)
        )
        for r in rows:
            uid = r["user_id"]
            st = Util.parseUTC(r["session_start"]).astimezone(TimeMgr.JST)
            ed = Util.parseUTC(r["session_end"]).astimezone(TimeMgr.JST)
            for key, seg_s, seg_e in Util.splitSessDay(st, ed):  # ← JST split
                if key in all_days:
                    user_day_sec[uid][key] += (seg_e - seg_s).total_seconds()

        # ---------- フォーマット & 並べ替え ----------
        def miss_and_msg(uid: int) -> tuple[int, str]:
            miss = [d for d in all_days if user_day_sec[uid].get(d, 0) < 180]
            name = (
                guild.get_member(uid).display_name
                if guild.get_member(uid)
                else str(uid)
            )
            if not miss:
                msg = f"✅ **{name}** : 全日クリア ({len(all_days)}日)"
            else:
                detail = ", ".join(
                    f"{d[5:]}:{int(user_day_sec[uid].get(d, 0))}s"
                    for d in miss[:5]
                )
                more = f" …(+{len(miss) - 5})" if len(miss) > 5 else ""
                msg = f"❌ **{name}** : {len(miss)} / {len(all_days)} 日不足 → {detail}{more}"
            return (len(miss), msg)

        # 不足日数が多い → 少ない → 最後に全日クリア順
        stats = [miss_and_msg(uid) for uid in target_uids]
        stats.sort(key=lambda t: (-t[0], t[1].lower()))

        # ---------- Embed 生成 ----------
        part_idx = 1
        lines_iter = iter([msg for _, msg in stats])
        while True:
            current = ""
            try:
                # Embed フィールド上限 (1024) に収まるだけ詰める
                while len(current) + len(peek := next(lines_iter) + "\n") <= 1024:
                    current += peek
            except StopIteration:
                pass

            if not current and stats:
                current = stats.pop(0)[1][:1021] + "…"

            embed = discord.Embed(
                title=f"{start_jst.year}年{start_jst.month}月 皆勤賞チェック"
                      + (f" (Part {part_idx})" if part_idx > 1 else ""),
                color=0x00BFFF,
                timestamp=TimeMgr.now_jst(),
            )
            embed.set_footer(
                text=(
                    "評価対象：月初〜月末"
                    if previous_month
                    else "評価対象：月初〜昨日／3 分(180s) 未満の日を不足扱い"
                )
            )
            embed.add_field(
                name="結果",
                value=current or "対象者なし",
                inline=False,
            )
            await interaction.followup.send(embed=embed, ephemeral=True)
            part_idx += 1

            if not current or all(
                    len(l) == 0 for l in lines_iter
            ):  # すべて送信し終えたら終了
                break

    # --- 一般ユーザー向けコマンド: description は空文字 ---
    @app_commands.command(name="rewards")
    async def rwdCmd(self, interaction: discord.Interaction) -> None:
        await interaction.response.defer(ephemeral=True)
        user, guild = interaction.user, interaction.guild
        if not guild or not self.bot.db: await interaction.followup.send("コマンドを利用できません。",
                                                                         ephemeral=True); return
        try:
            async with self.bot.db_lock:
                rows = await DBH.fetchAll(self.bot.db,
                                          "SELECT year, month, award_name FROM monthly_award_history WHERE guild_id=? AND user_id=? ORDER BY year DESC, month DESC",
                                          (guild.id, user.id))
            hist = defaultdict(list);
            [hist[r['award_name']].append(f"{r['year']}年{r['month']}月") for r in rows]
            lines = [f"**{user.mention} のリワードVC受賞歴**"] + (
                [f"- {award}: {', '.join(hist[award])}" for award in sorted(hist.keys())] if hist else [
                    "受賞実績: なし"])
            await interaction.followup.send("\n".join(lines), ephemeral=True)
        except Exception as e:
            logging.exception("Error fetching user rewards.")
            try:
                await interaction.followup.send("受賞履歴の取得中にエラーが発生しました.", ephemeral=True)
            except discord.NotFound:
                logging.error(f"Failed followup for rewards (int {interaction.id} expired).")
            except discord.HTTPException as he:
                logging.error(f"HTTPExc sending followup for rewards ({interaction.id}): {he}")

    @app_commands.command(name="monthly_award_list")
    async def mthAwdListCmd(self, interaction: discord.Interaction, year: int, month: int) -> None:
        await interaction.response.defer()
        guild = interaction.guild
        if not guild or not self.bot.db: await interaction.followup.send("コマンドを利用できません。",
                                                                         ephemeral=True); return
        if not (1 <= month <= 12): await interaction.followup.send("月は1から12の間で指定してください。",
                                                                   ephemeral=True); return
        try:
            async with self.bot.db_lock:
                rows = await DBH.fetchAll(self.bot.db,
                                          "SELECT award_name, user_id, value FROM monthly_award_history WHERE guild_id=? AND year=? AND month=? ORDER BY award_name",
                                          (guild.id, year, month))
            if not rows: await interaction.followup.send(f"{year}年{month}月の表彰データは見つかりません。",
                                                         ephemeral=True); return
            awards_data: Dict[str, Dict[str, List[Tuple[int, float]]]] = defaultdict(lambda: defaultdict(list))
            for row in rows: mem = guild.get_member(row['user_id']); sex = getSex(mem) if mem else "unknown";
            awards_data[row['award_name']][sex].append((row['user_id'], row['value']))
            embed = discord.Embed(title=f"{year}年{month}月度 表彰リスト (履歴)", color=0x1e90ff,
                                  timestamp=TimeMgr.now_jst());
            embed.set_footer(text="DB履歴からの表示")
            for award_name in sorted(awards_data.keys()):
                groups = awards_data[award_name];
                field_lines = []
                for gender, label in [("male", "男性"), ("female", "女性"), ("unknown", "その他")]:
                    user_values = sorted(groups.get(gender, []), key=lambda x: x[1], reverse=True)
                    field_lines.append(f"{label}: {Util.listOrNone(f'<@{uid}>' for uid, val in user_values)}")
                f_val = "\n".join(field_lines)
                if len(f_val) <= 1024:
                    embed.add_field(name=award_name, value=f_val, inline=False)
                else:
                    [embed.add_field(name=f"{award_name} (Part {i + 1})", value=chunk, inline=False) for i, chunk in
                     enumerate(Util.splitEmbed(f_val))]
            await interaction.followup.send(embed=embed)
        except Exception:
            logging.exception("vcAtTimeCmdでエラー発生")
            await interaction.followup.send("通話状況の確認中にエラーが発生しました。", ephemeral=True)
            logging.exception(f"Error fetching monthly award list for {year}-{month}.")
            await interaction.followup.send("表彰リストの取得中にエラーが発生しました。", ephemeral=True)

    # --- 管理者用コマンド: description を空文字 ---
    @app_commands.command(name="adm_rewards")
    @isAdmin()
    async def admRwdCmd(self, interaction: discord.Interaction, members: str) -> None:
        await interaction.response.defer(ephemeral=True)
        guild = interaction.guild
        if not guild or not self.bot.db: await interaction.followup.send("コマンドを利用できません。",
                                                                         ephemeral=True); return
        member_ids = re.findall(r"<@!?(\d+)>", members)
        if not member_ids: await interaction.followup.send("メンバーをメンションで指定してください。",
                                                           ephemeral=True); return
        target_uids = {int(mid) for mid in member_ids if mid.isdigit()}
        if not target_uids: await interaction.followup.send("有効なメンバーが見つかりません。", ephemeral=True); return
        results = []
        try:
            async with self.bot.db_lock:
                placeholders = ','.join('?' for _ in target_uids)
                query = f"SELECT user_id, year, month, award_name FROM monthly_award_history WHERE guild_id=? AND user_id IN ({placeholders}) ORDER BY user_id, year DESC, month DESC"
                rows = await DBH.fetchAll(self.bot.db, query, (guild.id,) + tuple(target_uids))
            user_hist: Dict[int, Dict[str, List[str]]] = defaultdict(lambda: defaultdict(list))
            for row in rows: user_hist[row['user_id']][row['award_name']].append(f"{row['year']}年{row['month']}月")
            for uid in target_uids:
                mention = guild.get_member(uid).mention if guild.get_member(uid) else f"<@{uid}>"
                lines = [f"**{mention} のリワードVC受賞歴**"] + (
                    [f"- {award}: {', '.join(hist[award])}" for award in sorted(hist.keys())] if (
                        hist := user_hist.get(uid)) else ["受賞実績なし"])
                results.append("\n".join(lines))
            chunks = Util.splitChunks("\n\n".join(results))
            await interaction.followup.send(chunks[0], ephemeral=True)
            for chunk in chunks[1:]: await interaction.followup.send(chunk, ephemeral=True)
        except Exception:
            logging.exception("vcAtTimeCmdでエラー発生")
            await interaction.followup.send("通話状況の確認中にエラーが発生しました。", ephemeral=True)
            logging.exception("Error fetching admin rewards.")
            await interaction.followup.send("受賞履歴の取得中にエラーが発生しました。", ephemeral=True)

    @app_commands.command(name="adm_current_awards")
    @isAdmin()
    async def admCurrAwdCmd(self, interaction: discord.Interaction) -> None:
        if not interaction.response.is_done():
            await interaction.response.defer(ephemeral=True)
        guild = interaction.guild
        if not guild or not self.bot.db:
            await interaction.followup.send("コマンドを利用できません。", ephemeral=True)
            return
        try:
            now_jst = TimeMgr.now_jst()
            awards = await AwardCalc.calcMonthly(self.bot, now_jst.year, now_jst.month, guild, until=None)
            if not awards:
                await interaction.followup.send("表彰データの計算中にエラーが発生しました。", ephemeral=True)
                return
            history = await AwardCalc.getAwardHist(self.bot, guild)
            # 男女別の embed を作成
            male_embed, female_embed = AwardCalc.mkAwardEmbeds(awards, now_jst.year, now_jst.month, history,
                                                               admin_view=True)
            male_embed.title = f"{now_jst.year}年{now_jst.month}月度 【男性】 表彰リスト (途中経過)"
            female_embed.title = f"{now_jst.year}年{now_jst.month}月度 【女性】 表彰リスト (途中経過)"
            await interaction.followup.send(embed=male_embed, ephemeral=True)
            await interaction.followup.send(embed=female_embed, ephemeral=True)
        except Exception as e:
            logging.exception("Error calculating current awards: %s", e)
            await interaction.followup.send(f"途中経過の計算中にエラーが発生しました。\n{e}", ephemeral=True)

    @app_commands.command(name="adm_weekly_longest_call")
    @isAdmin()
    async def admWkLCCmd(self, interaction: discord.Interaction, year: int, month: int) -> None:
        await interaction.response.defer()
        guild = interaction.guild
        if not guild or not self.bot.db: await interaction.followup.send("コマンドを利用できません。",
                                                                         ephemeral=True); return
        if not (1 <= month <= 12): await interaction.followup.send("月は1から12の間で指定してください。",
                                                                   ephemeral=True); return
        try:
            weekly_data = await AwardCalc.calcWeeklyLC(self.bot, year, month, guild)
            if not weekly_data: await interaction.followup.send(
                f"{year}年{month}月の週次データが見つからないか、計算エラーが発生しました。"); return
            embed = AwardCalc.mkWeeklyLCEmbed(weekly_data, year, month)
            await interaction.followup.send(embed=embed)
        except Exception:
            logging.exception("vcAtTimeCmdでエラー発生")
            await interaction.followup.send("通話状況の確認中にエラーが発生しました。", ephemeral=True)
            logging.exception(f"Error calculating weekly longest call for {year}-{month}.")
            await interaction.followup.send("週次最長通話の計算中にエラーが発生しました。")

    @app_commands.command(name="vc_at_time")
    @isAdmin()
    async def vcAtTimeCmd(self, interaction: discord.Interaction, time_jst_str: str) -> None:
        guild = interaction.guild
        if not guild or not self.bot.db: await interaction.response.send_message("コマンドを利用できません。",
                                                                                 ephemeral=True); return
        try:
            query_jst = datetime.strptime(time_jst_str, "%Y-%m-%d %H:%M").replace(
                tzinfo=TimeMgr.JST); query_utc = query_jst.astimezone(TimeMgr.UTC)
        except ValueError:
            await interaction.response.send_message("日時の形式が正しくありません。例: 2023-10-26 15:30",
                                                    ephemeral=True); return

        await interaction.response.defer(ephemeral=True)
        try:
            sessions = await Util.getSessAtTime(self.bot, query_utc)
            current_tracking = {}
            if abs((query_utc - TimeMgr.now_utc()).total_seconds()) < 300:
                current_tracking = {uid: data['channel_id'] for uid, data in self.bot.voice_state_tracking.items() if
                                    data.get('session_start') <= query_utc}
            if not sessions and not current_tracking: await interaction.followup.send(
                f"{time_jst_str} (JST) に通話中の記録はありません。", ephemeral=True); return
            channel_users: Dict[int, set[int]] = defaultdict(set)
            for user_id, channel_id in sessions: channel_users[channel_id].add(user_id)
            for user_id, channel_id in current_tracking.items(): channel_users[channel_id].add(user_id)
            lines = [f"**{time_jst_str} (JST) に通話中だったメンバー**"]
            for channel_id in sorted(channel_users.keys()):
                channel = guild.get_channel(channel_id);
                channel_mention = channel.mention if channel else f"不明ch (ID: {channel_id})"
                user_mentions = [guild.get_member(uid).mention if guild.get_member(uid) else f"<@{uid}>" for uid in
                                 sorted(channel_users[channel_id])]
                lines.extend([f"\n**{channel_mention}**", " - " + ", ".join(user_mentions)])
            chunks = Util.splitChunks("\n".join(lines))
            await interaction.followup.send(chunks[0], ephemeral=True)
            for chunk in chunks[1:]: await interaction.followup.send(chunk, ephemeral=True)
        except Exception:
            logging.exception("vcAtTimeCmdでエラー発生")
            await interaction.followup.send("通話状況の確認中にエラーが発生しました。", ephemeral=True)

    @app_commands.command(name="callstats")
    @isAdmin()
    async def callStatsCmd(self, interaction: discord.Interaction, members: str) -> None:
        if not interaction.response.is_done():
            await interaction.response.defer(ephemeral=True)
        guild = interaction.guild
        if not guild or not self.bot.db:
            await interaction.followup.send("コマンドを利用できません。", ephemeral=True)
            return

        member_ids = re.findall(r"<@!?(\d+)>", members)
        target_uids = {int(mid) for mid in member_ids if mid.isdigit()}

        if len(target_uids) == 1:
            # 1名指定時: その人と同席した全ユーザーとの重複時間ランキング
            main_uid = next(iter(target_uids))
            main_member = guild.get_member(main_uid)
            if not main_member:
                await interaction.followup.send("指定ユーザーがサーバーにいません。", ephemeral=True)
                return
            try:
                async with self.bot.db_lock:
                    rows = await DBH.fetchAll(
                        self.bot.db,
                        "SELECT user_id, channel_id, session_start, session_end FROM voice_session_logs_reward"
                    )
                # 指定ユーザーの全セッション取得
                main_sessions = [
                    {"channel_id": row['channel_id'], "start": Util.parseUTC(row['session_start']),
                     "end": Util.parseUTC(row['session_end'])}
                    for row in rows if row['user_id'] == main_uid
                ]
                # 他ユーザーのセッションも取得
                from collections import defaultdict
                others_sessions = defaultdict(list)
                for row in rows:
                    uid = row['user_id']
                    if uid == main_uid:
                        continue
                    try:
                        others_sessions[uid].append({
                            "channel_id": row['channel_id'],
                            "start": Util.parseUTC(row['session_start']),
                            "end": Util.parseUTC(row['session_end'])
                        })
                    except Exception as e:
                        logging.warning(f"Skipping invalid session for {uid}: {row} - {e}")
                # 重複時間計算
                overlap_stats = defaultdict(lambda: {"total_duration": 0.0, "call_count": 0})
                for sess1 in main_sessions:
                    ch1, st1, ed1 = sess1["channel_id"], sess1["start"], sess1["end"]
                    overlapped_users = set()
                    for uid, sessions in others_sessions.items():
                        for sess2 in sessions:
                            if sess2["channel_id"] == ch1 and st1 < sess2["end"] and sess2["start"] < ed1:
                                overlap_sec = max(0,
                                                  (min(ed1, sess2["end"]) - max(st1, sess2["start"])).total_seconds())
                                if overlap_sec > 0:
                                    overlap_stats[uid]["total_duration"] += overlap_sec
                                    overlapped_users.add(uid)
                    for uid in overlapped_users:
                        overlap_stats[uid]["call_count"] += 1
                # 結果を重複時間順に
                lines = []
                for uid, stat in sorted(overlap_stats.items(), key=lambda item: item[1]["total_duration"],
                                        reverse=True):
                    # bot自身は除外
                    if uid == self.bot.user.id:
                        continue
                    member = guild.get_member(uid)
                    if not member or stat["total_duration"] <= 0:
                        continue
                    # 相手の名前だけ表示
                    lines.append(
                        f"**{member.display_name}**: {Util.fmtDur(int(stat['total_duration']))} ({stat['call_count']}回)")
                embed = discord.Embed(title=f"{main_member.display_name}さんと同席したユーザー重複時間ランキング",
                                      color=0x00ff00, timestamp=TimeMgr.now_jst())
                embed.description = f"対象: {main_member.mention}"
                embed.set_footer(text="BOT自動集計 | 重複回数は参考値")
                if not lines:
                    embed.add_field(name="結果", value="同席したユーザーとの重複通話記録はありませんでした。",
                                    inline=False)
                else:
                    chunks = Util.splitEmbed("\n".join(lines))
                    for i, chunk in enumerate(chunks):
                        embed.add_field(name="重複統計" + (f" (Part {i + 1})" if i > 0 else ""), value=chunk,
                                        inline=False)
                await interaction.followup.send(embed=embed, ephemeral=True)
            except Exception:
                logging.exception("vcAtTimeCmdでエラー発生")
                await interaction.followup.send("通話状況の確認中にエラーが発生しました。", ephemeral=True)
                logging.exception("Error calculating callstats (1 user mode).")
                await interaction.followup.send("通話統計の計算中にエラーが発生しました。", ephemeral=True)
            return

        # 2名以上指定時
        if len(target_uids) < 2:
            await interaction.followup.send("メンバーを1人以上メンションで指定してください。", ephemeral=True)
            return

        try:
            async with self.bot.db_lock:
                rows = await DBH.fetchAll(
                    self.bot.db,
                    "SELECT user_id, channel_id, session_start, session_end FROM voice_session_logs_reward"
                )
            # 有効なメンバーのみ抽出
            valid_members = {uid: mem for uid, mem in {uid: guild.get_member(uid) for uid in target_uids}.items() if
                             mem}
            if len(valid_members) < 2:
                await interaction.followup.send("指定メンバーの一部または全員がサーバーにいません。", ephemeral=True)
                return
            from collections import defaultdict
            user_sessions = defaultdict(list)
            for row in rows:
                if row['user_id'] in target_uids:
                    try:
                        user_sessions[row['user_id']].append({
                            "channel_id": row['channel_id'],
                            "start": Util.parseUTC(row['session_start']),
                            "end": Util.parseUTC(row['session_end'])
                        })
                    except Exception as e:
                        logging.warning(f"Skipping invalid session for {row['user_id']}: {row} - {e}")
            overlap_stats = defaultdict(lambda: {"total_duration": 0.0, "call_count": 0})
            target_uid_list = sorted(list(target_uids))
            for i in range(len(target_uid_list)):
                uid1 = target_uid_list[i];
                sessions1 = user_sessions.get(uid1, [])
                if not sessions1:
                    continue
                for j in range(i + 1, len(target_uid_list)):
                    uid2 = target_uid_list[j];
                    sessions2 = user_sessions.get(uid2, [])
                    if not sessions2:
                        continue
                    pair = tuple(sorted((uid1, uid2)));
                    pair_overlap_duration = 0.0;
                    overlap_count_approx = 0
                    for sess1 in sessions1:
                        ch1, st1, ed1 = sess1["channel_id"], sess1["start"], sess1["end"];
                        session1_overlapped = False
                        for sess2 in sessions2:
                            if sess2["channel_id"] == ch1 and st1 < sess2["end"] and sess2["start"] < ed1:
                                pair_overlap_duration += max(0, (
                                            min(ed1, sess2["end"]) - max(st1, sess2["start"])).total_seconds())
                                session1_overlapped = True
                        if session1_overlapped:
                            overlap_count_approx += 1
                    overlap_stats[pair]["total_duration"] += pair_overlap_duration
                    overlap_stats[pair]["call_count"] += overlap_count_approx
            embed = discord.Embed(title="指定メンバー間のリワードVC重複通話統計", color=0x00ff00,
                                  timestamp=TimeMgr.now_jst())
            embed.description = f"対象: {', '.join(valid_members[uid].mention for uid in target_uid_list)}"
            embed.set_footer(text="BOT自動集計 | 重複回数は参考値")
            if not overlap_stats:
                embed.add_field(name="結果", value="指定メンバー間での重複通話記録はありませんでした。", inline=False)
            else:
                lines = [
                    f"**{valid_members[p[0]].display_name} & {valid_members[p[1]].display_name}**: {Util.fmtDur(int(s['total_duration']))} ({s['call_count']}回)"
                    for p, s in sorted(overlap_stats.items(), key=lambda item: item[1]["total_duration"], reverse=True)
                    if valid_members.get(p[0]) and valid_members.get(p[1])]
                chunks = Util.splitEmbed("\n".join(lines))
                for i, chunk in enumerate(chunks):
                    embed.add_field(name="重複統計" + (f" (Part {i + 1})" if i > 0 else ""), value=chunk, inline=False)
            await interaction.followup.send(embed=embed, ephemeral=True)
        except Exception:
            logging.exception("vcAtTimeCmdでエラー発生")
            await interaction.followup.send("通話状況の確認中にエラーが発生しました。", ephemeral=True)
            logging.exception("Error calculating call stats.")
            await interaction.followup.send("通話統計の計算中にエラーが発生しました。", ephemeral=True)
        return

    @app_commands.command(name="help")
    @isAdmin()
    async def helpCmd(self, interaction: discord.Interaction) -> None:
        await interaction.response.defer(ephemeral=True)
        # ... (unchanged code)
        embed = discord.Embed(title="管理者向けコマンド一覧", color=discord.Color.blue());
        embed.set_footer(text=f"Bot Version: {getattr(self.bot, 'version', 'N/A')}")
        commands_desc = {
            "/rewards": "自分のリワードVC受賞履歴を表示します。",
            "/monthly_award_list year: month:": "",
            "/adm_rewards members:": "",
            "/adm_current_awards": "",
            "/year: month:": "",
            "/vc_at_time time_jst_str:": "",
            "/callstats members:": "",
            "/adm_publish_monthly_awards year: month:": "",
            "/reward_exclude add members: [reason:]": "",
            "/reward_exclude remove members:": "",
            "/reward_exclude list": "",
            "/help": ""
        }
        help_text = "\n\n".join(f"{name}\n{desc}" for name, desc in commands_desc.items())
        chunks = Util.splitEmbed(help_text.strip(), 4096);
        embed.description = chunks[0]
        await interaction.followup.send(embed=embed, ephemeral=True)
        for chunk in chunks[1:]: await interaction.followup.send(chunk, ephemeral=True)

    @app_commands.command(name="adm_publish_monthly_awards")
    @isAdmin()
    async def adm_publish_monthly_awards_cmd(self, interaction: discord.Interaction, year: int, month: int) -> None:
        await interaction.response.defer(ephemeral=True)
        guild = interaction.guild
        if not guild or not self.bot.db:
            await interaction.followup.send("コマンドを利用できません。", ephemeral=True)
            return
        if not (1 <= month <= 12):
            await interaction.followup.send("月は1～12の範囲で指定してください。", ephemeral=True)
            return
        target_channel = guild.get_channel(TEST_CHANNEL_ID)
        if not isinstance(target_channel, discord.TextChannel):
            await interaction.followup.send(f"投稿先チャンネル ({TEST_CHANNEL_ID}) が見つかりません。", ephemeral=True)
            return
        try:
            end_jst_month = datetime(year + (month // 12), (month % 12) + 1, 1, tzinfo=TimeMgr.JST)
            until_utc = end_jst_month.astimezone(TimeMgr.UTC)
            awards = await AwardCalc.calcMonthly(self.bot, year, month, guild, until=until_utc)
            if not awards: await interaction.followup.send(f"{year}年{month}月の表彰データの計算中にエラー。"); return
            history = await AwardCalc.getAwardHist(self.bot, guild)
            # 男女別に embed を生成
            male_embed, female_embed = AwardCalc.mkAwardEmbeds(awards, year, month, history, admin_view=False)
            await target_channel.send(embed=male_embed)
            await target_channel.send(embed=female_embed)
            await AwardCalc.saveMonthlyHist(self.bot, awards, guild.id, year, month)
            await interaction.followup.send(
                f"{year}年{month}月の表彰リストを {target_channel.mention} へ投稿し、履歴を保存しました。",
                ephemeral=True)
        except Exception as e:
            logging.exception(f"Error publishing monthly awards for {year}-{month}.")
            await interaction.followup.send(f"表彰リストの投稿/保存中にエラー発生: {e}", ephemeral=True)


# ======================= 皆勤スタンプカード =======================
STAMP_TARGET_ID: int = 1367666049130041374  # 投稿チャンネル or スレッド ID
STAMP_UPDATE_INTERVAL_SEC = 60 * 30  # 自動更新間隔（30 分）
NEEDED_SEC_PER_DAY = 180  # 皆勤判定 = 3 分


def _fmt_stamp_row(member: discord.Member, stamps: list[bool], col_w: int) -> str:
    name = member.display_name[:col_w].ljust(col_w, " ")
    marks = " ".join("✅" if ok else "▫" for ok in stamps)
    return f"{name} │ {marks}"


async def _calc_attendance_matrix(
        bot: "MyBot",
        guild: discord.Guild,
        year: int,
        month: int,
) -> tuple[str, list[int]]:
    """

text
 で掲示可能な“表の本文”(ヘッダ含む)と
    日付番号リスト (1–31) を返す
    """
    JST, UTC = TimeMgr.JST, TimeMgr.UTC
    start_jst = datetime(year, month, 1, tzinfo=JST)
    next_y, next_m = (year + 1, 1) if month == 12 else (year, month + 1)
    end_jst = datetime(next_y, next_m, 1, tzinfo=JST)

    today_jst = TimeMgr.now_jst().date()
    last_date = min((end_jst - timedelta(days=1)).date(), today_jst)
    days_list = [
        (start_jst.date() + timedelta(days=i))
        for i in range((last_date - start_jst.date()).days + 1)
    ]
    if not days_list:
        return "", []

    async with bot.db_lock:
        rows = await DBH.fetchAll(
            bot.db,
            """
            SELECT user_id, session_start, session_end
            FROM voice_session_logs_reward
            WHERE session_end > ?
              AND session_start < ?
            """,
            (
                Util.dtStr(start_jst.astimezone(UTC)),
                Util.dtStr(end_jst.astimezone(UTC)),
            ),
        )

    # 秒数集計
    day_key = lambda d: d.strftime("%Y-%m-%d")
    user_day_sec: dict[int, dict[str, float]] = defaultdict(lambda: defaultdict(float))
    for r in rows:
        uid = r["user_id"]
        st = Util.parseUTC(r["session_start"]).astimezone(JST)
        ed = Util.parseUTC(r["session_end"]).astimezone(JST)
        for key, seg_s, seg_e in Util.splitSessDay(st, ed):
            if key in {day_key(d) for d in days_list}:
                user_day_sec[uid][key] += (seg_e - seg_s).total_seconds()

    # 対象メンバー
    role_ids = set(MALE_ROLES + FEMALE_ROLES +
                   [EXTRA_ATTEND_MALE_ROLE_ID, EXTRA_ATTEND_FEMALE_ROLE_ID])
    members = [
        m for m in guild.members
        if not m.bot and any(r.id in role_ids for r in m.roles)
    ]
    members.sort(key=lambda m: (len(ok_map[m.id]), m.display_name.lower(), m.id))

    # 本文
    header = " " * 14 + " | " + "".join(f"{d.day:02d}" for d in days_list)
    body = "\n".join(
        _fmt_stamp_row(
            m,
            [
                user_day_sec[m.id].get(day_key(d), 0.0) >= 180
                for d in days_list
            ],
        )
        for m in members
    )
    return f"{header}\n{body}", [d.day for d in days_list]


# --------------------------------------------------------------------
# Discord API コールを “安全に” 実行する共通ラッパ
#   ・HTTP 429 が返ったら e.retry_after 秒 (+ジッター) だけ待ってリトライ
#   ・その他 HTTPException は呼び出し側にそのまま投げる
#   ・最大 5 回までリトライしても成功しなければ RuntimeError
# --------------------------------------------------------------------

async def safe_api_call(coro_func, *args, **kwargs):
    MAX_RETRY = 5
    for attempt in range(1, MAX_RETRY + 1):
        try:
            return await coro_func(*args, **kwargs)
        except discord.HTTPException as e:
            if e.status != 429:
                raise  # 429 以外は即エラー
            wait_for = getattr(e, "retry_after", 5.0) + random.uniform(0.15, 0.5)
            logging.warning(
                f"[safe_api_call] 429 (attempt {attempt}/{MAX_RETRY}) – "
                f"sleep {wait_for:.2f}s then retry")
            await asyncio.sleep(wait_for)
    raise RuntimeError("safe_api_call: exceeded max retries")


# ─── 追加インポート ─────────────────────────────
from io import BytesIO
from PIL import Image, ImageDraw, ImageFont

# フォントはシステムに入っている等幅系を探して下さい
DEFAULT_FONT_PATH = "C:\\Windows\\Fonts\\msgothic.ttc"  # 例: Windows

# ======================= 皆勤スタンプカード =======================
import json
from collections import defaultdict

# ── 定数 ----------------------------------------------------------
STAMP_TARGET_ID = 1367666049130041374  # 投稿チャンネル or スレッド ID
STAMP_UPDATE_INTERVAL_SEC = 60 * 30  # 自動更新間隔（30 分）
NEEDED_SEC_PER_DAY = 180  # 皆勤判定 = 3 分
ATTENDANCE_STATE_FILE = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "attendance_board_state.json",
)


# -----------------------------------------------------------------


class AttendanceBoard(commands.Cog):
    """
    皆勤スタンプカード（日付 × マス方式）

    ● 月替わりごとに新しいメッセージ列を生成
    ● Bot 再起動後も以前のメッセージを編集して上書き（白紙化しない）
    """
    OK_MARK = "🟩"
    NG_MARK = "⬜"
    # TODAY_OK_MARK と TODAY_NG_MARK は _build_embeds 内で直接指定するため不要

    MAX_DESC = 3900  # Embed.description 上限 4096 からマージン確保
    MAX_USERS = 6  # 1 Embed に表示するユーザー数

    def __init__(self, bot: "MyBot") -> None:
        self.bot = bot
        self.current_year_month: tuple[int, int] | None = None
        self.last_msg_ids: list[int] = []  # ← 最新 Embed の message IDs
        self.auto_task.start()

    # -------------------------------------------------------------
    # 永続化 (message IDs と対象年月)
    # -------------------------------------------------------------
    async def _load_state(self) -> None:
        try:
            with open(ATTENDANCE_STATE_FILE, "r", encoding="utf-8") as fp:
                data = json.load(fp)
            ym = tuple(data.get("ym", []))
            if len(ym) == 2:
                self.current_year_month = (int(ym[0]), int(ym[1]))
            self.last_msg_ids = [int(x) for x in data.get("msg_ids", [])]
            logging.info(f"[AttendanceBoard] state loaded: {self.last_msg_ids}")
        except FileNotFoundError:
            logging.info("[AttendanceBoard] first run – state file absent")
        except Exception:
            logging.exception("[AttendanceBoard] failed to load state")

    def _save_state(self) -> None:
        try:
            data = {
                "ym": list(self.current_year_month or []),
                "msg_ids": self.last_msg_ids,
            }
            with open(ATTENDANCE_STATE_FILE, "w", encoding="utf-8") as fp:
                json.dump(data, fp)
        except Exception:
            logging.exception("[AttendanceBoard] failed to save state")

    # -------------------------------------------------------------
    # データ収集
    # -------------------------------------------------------------
    async def _collect(
            self,
            guild: discord.Guild,
            year: int,
            month: int,
    ) -> tuple[list[discord.Member], list[int], dict[int, set[int]], int | None]:
        """
        対象月の通話ログを集計し、
        - members   : ソート済みメンバー一覧
        - day_nums  : [1, 2, …, 月末日]
        - ok_map    : {uid: {OK 日番号, …}}
        - today_num : 今日の日付番号 (該月でなければ None)
        を返す
        """
        JST, UTC = TimeMgr.JST, TimeMgr.UTC

        # ── 対象月の期間 (★月末まで表示するように変更) ──────────────────
        start_jst = datetime(year, month, 1, tzinfo=JST)
        next_y, next_m = (year + 1, 1) if month == 12 else (year, month + 1)
        end_jst_month = datetime(next_y, next_m, 1, tzinfo=JST)

        last_date_of_month = (end_jst_month - timedelta(days=1)).date()
        days = [
            start_jst.date() + timedelta(days=i)
            for i in range((last_date_of_month - start_jst.date()).days + 1)
        ]

        day_keys = {d.strftime("%Y-%m-%d") for d in days}

        # 今日の日付を特定
        today_date = TimeMgr.now_jst().date()
        today_num = today_date.day if today_date.year == year and today_date.month == month else None

        # ── 通話ログ取得 ─────────────────────────────
        async with self.bot.db_lock:
            rows = await DBH.fetchAll(
                self.bot.db,
                """
                SELECT user_id, session_start, session_end
                FROM voice_session_logs_reward
                WHERE session_end > ?
                  AND session_start < ?
                """,
                (
                    Util.dtStr(start_jst.astimezone(UTC)),
                    Util.dtStr(end_jst_month.astimezone(UTC)),
                ),
            )

        # ── 日別秒数集計 ─────────────────────────────
        user_day_sec: dict[int, dict[str, float]] = defaultdict(
            lambda: defaultdict(float)
        )
        for r in rows:
            uid = r["user_id"]
            st = Util.parseUTC(r["session_start"]).astimezone(JST)
            ed = Util.parseUTC(r["session_end"]).astimezone(JST)
            for key, seg_s, seg_e in Util.splitSessDay(st, ed):
                if key in day_keys:
                    user_day_sec[uid][key] += (seg_e - seg_s).total_seconds()

        # ── 対象メンバー抽出 ──────────────────────────
        role_ids = set(
            MALE_ROLES
            + FEMALE_ROLES
            + [EXTRA_ATTEND_MALE_ROLE_ID, EXTRA_ATTEND_FEMALE_ROLE_ID]
        )
        members = [
            m
            for m in guild.members
            if (not m.bot) and any(r.id in role_ids for r in m.roles)
        ]

        # OK 日マップ
        ok_map = {
            m.id: {
                int(k[-2:])  # yd-MM-**DD**
                for k, sec in user_day_sec[m.id].items()
                if sec >= NEEDED_SEC_PER_DAY
            }
            for m in members
        }

        # 出席ゼロは除外
        members = [m for m in members if ok_map.get(m.id)]

        # 緑が少ない順 → 名前順
        members.sort(key=lambda m: (len(ok_map[m.id]), m.display_name.lower()))

        return members, [d.day for d in days], ok_map, today_num

    # -------------------------------------------------------------
    # ヘッダ・行生成
    # -------------------------------------------------------------
    @staticmethod
    def _header_line(day_nums: list[int]) -> str:
        return "    " + "".join(f"{d:02d}" for d in day_nums)

    def _bar_line(self, day_nums: list[int], ok_days: set[int]) -> str:
        return "".join(self.OK_MARK if d in ok_days else self.NG_MARK for d in day_nums)

    # -------------------------------------------------------------
    # Embed 作成（ヘッダ行を完全に削除した版）
    # -------------------------------------------------------------
    def _build_embeds(
            self,
            members: list[discord.Member],
            day_nums: list[int],
            ok_map: dict[int, set[int]],
            title: str,
            today_num: int | None,
    ) -> list[discord.Embed]:
        """
        ・日付のヘッダ行（01‥31）を出さないシンプル表示
        """
        embeds: list[discord.Embed] = []

        part_idx = 1
        buf = ""
        user_cnt = 0

        def flush():
            nonlocal buf, user_cnt, part_idx
            if not buf.strip():
                return
            em = discord.Embed(
                title=title if part_idx == 1 else "",
                description=buf.rstrip("\n"),
                color=0x57F287,
            )
            em.set_footer(text=f"最終更新: {TimeMgr.now_jst():%Y-%m-%d %H:%M}")
            embeds.append(em)
            buf = ""
            user_cnt = 0
            part_idx += 1

        for m in members:
            name = f"**{m.display_name}**"
            ok_days = ok_map.get(m.id, set())

            bar_parts = []
            for d in day_nums:
                is_ok = d in ok_days
                is_today = d == today_num

                if is_today:
                    # ★ご指定のアイコンに変更
                    bar_parts.append("✅" if is_ok else "🟥")
                else:
                    bar_parts.append(self.OK_MARK if is_ok else self.NG_MARK)

            bar = "".join(bar_parts)
            entry = f"{name}\n{bar}\n\n"

            # ページ分割チェック
            if (
                    user_cnt >= self.MAX_USERS
                    or len(buf) + len(entry) > self.MAX_DESC
            ):
                flush()

            buf += entry
            user_cnt += 1

        flush()
        return embeds

    # -------------------------------------------------------------
    # Discord メッセージ操作
    # -------------------------------------------------------------
    async def _resolve_target(
            self, guild: discord.Guild
    ) -> discord.abc.Messageable | None:
        tgt = guild.get_channel(STAMP_TARGET_ID)
        if tgt is None:
            try:
                tgt = await self.bot.fetch_channel(STAMP_TARGET_ID)
            except (discord.NotFound, discord.Forbidden):
                return None

        if isinstance(tgt, discord.Thread):
            try:
                await tgt.edit(archived=False, locked=False)
                if not tgt.me:
                    await tgt.join()
            except discord.Forbidden:
                return None
        return tgt

    async def _send_embeds(
            self, target: discord.abc.Messageable, embeds: list[discord.Embed]
    ) -> None:
        """既存 Embed を編集・追補し、余分は削除"""

        def same(desc1: str | None, desc2: str | None) -> bool:
            return (desc1 or "").strip() == (desc2 or "").strip()

        cached: list[discord.Message | None] = []
        for mid in self.last_msg_ids:
            try:
                cached.append(await target.fetch_message(mid))
            except (discord.NotFound, discord.Forbidden):
                cached.append(None)

        new_ids: list[int] = []

        for idx, embed in enumerate(embeds):
            msg = cached[idx] if idx < len(cached) else None
            if (
                    msg
                    and msg.embeds
                    and same(msg.embeds[0].description, embed.description)
            ):
                new_ids.append(msg.id)  # 未変更
                continue

            if msg:
                new_ids.append(
                    (await safe_api_call(msg.edit, embed=embed)).id
                )
            else:
                new_ids.append(
                    (await safe_api_call(target.send, embed=embed)).id
                )
            await asyncio.sleep(1.1)  # 5 req / 5 s 制限を確実に回避

        # 余分を削除
        for old_msg_id in self.last_msg_ids[len(embeds):]:
            try:
                msg_to_del = await target.fetch_message(old_msg_id)
                await safe_api_call(msg_to_del.delete)
                await asyncio.sleep(1.1)
            except (discord.NotFound, discord.Forbidden):
                pass

        self.last_msg_ids = new_ids
        self._save_state()  # ← 状態を保存

    # -------------------------------------------------------------
    # 自動更新タスク
    # -------------------------------------------------------------
    @tasks.loop(seconds=STAMP_UPDATE_INTERVAL_SEC)
    async def auto_task(self):
        await self.bot.wait_until_ready()

        guild = self.bot.get_guild(GUILD_ID)
        if guild is None or self.bot.db is None:
            return

        now = TimeMgr.now_jst()
        ym = (now.year, now.month)

        if self.current_year_month != ym:
            # 月替わり → 新しい列を作る
            self.current_year_month = ym
            self.last_msg_ids = []

        try:
            members, day_nums, ok_map, today_num = await self._collect(guild, *ym)
            if not members:
                return

            title = f"{ym[0]}年{ym[1]}月 皆勤スタンプカード"
            embeds = self._build_embeds(members, day_nums, ok_map, title, today_num)
            target = await self._resolve_target(guild)
            if target is None:
                logging.error("[AttendanceBoard] target not found")
                return

            await self._send_embeds(target, embeds)
        except Exception:
            logging.exception("[AttendanceBoard] auto-update error")

    @auto_task.before_loop
    async def before_auto(self):  # noqa: D401
        await self._load_state()
        await self.bot.wait_until_ready()

    # -------------------------------------------------------------
    # 手動更新コマンド
    # -------------------------------------------------------------
    @app_commands.command(name="adm_attendance_board")
    @isAdmin()
    async def adm_attendance_board(
            self,
            interaction: discord.Interaction,
            year: int | None = None,
            month: int | None = None,
    ):
        await interaction.response.defer(ephemeral=True)
        guild = interaction.guild
        if guild is None:
            await interaction.followup.send("ギルドが取得できません。", ephemeral=True)
            return

        now = TimeMgr.now_jst()
        y, m = year or now.year, month or now.month

        try:
            members, day_nums, ok_map, today_num = await self._collect(guild, y, m)
            if not members:
                await interaction.followup.send("対象データがありません。", ephemeral=True)
                return

            title = f"{y}年{m}月 皆勤スタンプカード"
            embeds = self._build_embeds(members, day_nums, ok_map, title, today_num)
            target = await self._resolve_target(guild)
            if target is None:
                await interaction.followup.send("投稿先が見つかりません。", ephemeral=True)
                return

            await self._send_embeds(target, embeds)
            await interaction.followup.send("スタンプカードを投稿しました。", ephemeral=True)
        except Exception:
            logging.exception("[AttendanceBoard] manual post error")
            await interaction.followup.send("生成に失敗しました。", ephemeral=True)


# ---------- Cog 登録ヘルパー ----------
async def setup_attendance_board(bot: "MyBot") -> None:
    await bot.add_cog(AttendanceBoard(bot))


@app_commands.command(name="adm_remove_profile_submission")
@isAdmin()
async def adm_remove_profile_submission(
        interaction: discord.Interaction,
        member: discord.Member,
) -> None:
    """指定メンバーの profile_submission_log を手動で削除"""
    await interaction.response.defer(ephemeral=True)
    if not interaction.client.db:
        await interaction.followup.send("DB 未接続のため操作できません。", ephemeral=True)
        return

    async with interaction.client.db_lock:
        await interaction.client.db.execute(
            "DELETE FROM profile_submission_log WHERE user_id = ?",
            (member.id,),
        )
    await interaction.followup.send(
        f"✅ {member.mention} のプロフィール提出レコードを削除しました。",
        ephemeral=True,
    )


# --- /reward_exclude グループ ---
reward_exclude_group = app_commands.Group(name="reward_exclude", description="リワード除外に関するコマンド",
                                          guild_ids=[GUILD_ID] if GUILD_ID else None)


@reward_exclude_group.command(name="add")
@isAdmin()
async def exclude_add(interaction: discord.Interaction, members: str, reason: Optional[str] = None) -> None:
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild;
    client = interaction.client
    if not guild or not client.db: await interaction.followup.send("コマンド利用不可", ephemeral=True); return
    member_ids = re.findall(r"<@!?(\d+)>", members)
    if not member_ids: await interaction.followup.send("メンバーをメンション指定", ephemeral=True); return
    target_uids = {int(mid) for mid in member_ids if mid.isdigit()}
    if not target_uids: await interaction.followup.send("有効なメンバーが見つかりません", ephemeral=True); return
    now_utc_str = Util.dtStr(TimeMgr.now_utc())
    try:
        params = [(guild.id, uid, reason or "", now_utc_str) for uid in target_uids]
        async with client.db_lock:
            await client.db.executemany("INSERT OR IGNORE INTO reward_exclusions VALUES (?, ?, ?, ?)", params);
        await interaction.followup.send(
            f"以下をリワード除外しました(既存含む):\n{Util.listOrNone(f'<@{uid}>' for uid in target_uids)}",
            ephemeral=True)
    except Exception:
        logging.exception("Error adding reward exclusions.")
        await interaction.followup.send("除外リスト追加エラー", ephemeral=True)


@reward_exclude_group.command(name="remove")
@isAdmin()
async def exclude_remove(interaction: discord.Interaction, members: str) -> None:
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild;
    client = interaction.client
    if not guild or not client.db: await interaction.followup.send("コマンド利用不可", ephemeral=True); return
    member_ids = re.findall(r"<@!?(\d+)>", members)
    if not member_ids: await interaction.followup.send("メンバーをメンション指定", ephemeral=True); return
    target_uids = {int(mid) for mid in member_ids if mid.isdigit()}
    if not target_uids: await interaction.followup.send("有効なメンバーが見つかりません", ephemeral=True); return
    try:
        params = [(guild.id, uid) for uid in target_uids]
        async with client.db_lock:
            await client.db.executemany("DELETE FROM reward_exclusions WHERE guild_id = ? AND user_id = ?", params);
        await interaction.followup.send(
            f"以下のリワード除外を解除しました(未除外含む):\n{Util.listOrNone(f'<@{uid}>' for uid in target_uids)}",
            ephemeral=True)
    except Exception:
        logging.exception("Error removing reward exclusions.")
        await interaction.followup.send("除外リスト削除エラー", ephemeral=True)


@reward_exclude_group.command(name="list")
@isAdmin()
async def exclude_list(interaction: discord.Interaction) -> None:
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild;
    client = interaction.client
    if not guild or not client.db: await interaction.followup.send("コマンド利用不可", ephemeral=True); return
    try:
        async with client.db_lock:
            rows = await DBH.fetchAll(client.db,
                                      "SELECT user_id, reason, added_at FROM reward_exclusions WHERE guild_id = ? ORDER BY added_at DESC",
                                      (guild.id,))
        if not rows: await interaction.followup.send("現在リワード除外中のメンバーはいません。", ephemeral=True); return
        lines = ["**リワード除外リスト**"]
        for row in rows:
            mention = guild.get_member(row['user_id']).mention if guild.get_member(
                row['user_id']) else f"<@{row['user_id']}>"
            try:
                added_jst_str = TimeMgr.to_jst(Util.parseUTC(row['added_at'])).strftime('%Y-%m-%d %H:%M JST')
            except Exception:
                added_jst_str = row['added_at'] + " UTC"
            lines.append(f"- {mention} (理由: {row['reason'] or 'なし'}, 追加: {added_jst_str})")
        chunks = Util.splitChunks("\n".join(lines))
        await interaction.followup.send(chunks[0], ephemeral=True)
        for chunk in chunks[1:]: await interaction.followup.send(chunk, ephemeral=True)
    except Exception:
        logging.exception("Error listing reward exclusions.")
        await interaction.followup.send("除外リスト取得エラー", ephemeral=True)


# --- 定期実行タスク（途中経過：毎月13日 12:00 JST）---
async def midMonthLoop(bot: MyBot) -> None:
    """
    毎月 13 日 12:00 (JST) に途中経過を投稿するループ。
    再起動や長時間スリープ後でも必ず次回時刻を再計算する。
    """
    await bot.wait_until_ready()
    logging.info("[Mid-Month Task] Started (13th 12:00 JST).")

    TARGET_DAY = 13  # 13 日
    TARGET_HOUR = 12  # 12:00
    TARGET_MIN = 0

    while not bot.is_closed():
        now_jst = TimeMgr.now_jst()

        # ── 次回実行日時を決定 ──
        if (now_jst.day < TARGET_DAY
                or (now_jst.day == TARGET_DAY
                    and (now_jst.hour, now_jst.minute) < (TARGET_HOUR, TARGET_MIN))):
            # 今月 13 日 12:00
            next_run_dt = now_jst.replace(day=TARGET_DAY,
                                          hour=TARGET_HOUR,
                                          minute=TARGET_MIN,
                                          second=0, microsecond=0)
        else:
            # 翌月 13 日 12:00
            first_of_next = (now_jst.replace(day=28) + timedelta(days=4)).replace(day=1)
            next_run_dt = first_of_next.replace(day=TARGET_DAY,
                                                hour=TARGET_HOUR,
                                                minute=TARGET_MIN,
                                                second=0, microsecond=0)

        wait_seconds = (next_run_dt - now_jst).total_seconds()
        logging.info(f"[Mid-Month Task] Next run at {next_run_dt.isoformat()} "
                     f"(sleep {wait_seconds:.0f}s)")
        await asyncio.sleep(wait_seconds)

        # ── 途中経過を投稿 ──
        try:
            guild = bot.get_guild(GUILD_ID)
            channel = guild.get_channel(TEST_CHANNEL_ID) if guild else None
            if not guild or not bot.db or not isinstance(channel, discord.TextChannel):
                logging.error("[Mid-Month Task] Guild / DB / Channel not ready.")
                continue

            awards = await AwardCalc.calcMonthly(bot,
                                                 next_run_dt.year,
                                                 next_run_dt.month,
                                                 guild)
            history = await AwardCalc.getAwardHist(bot, guild)
            male_e, female_e = AwardCalc.mkAwardEmbeds(
                awards, next_run_dt.year, next_run_dt.month,
                history, admin_view=False)
            male_e.title += " (途中経過)"
            female_e.title += " (途中経過)"
            await channel.send(embed=male_e)
            await channel.send(embed=female_e)
            logging.info("[Mid-Month Task] Report sent.")
        except Exception:
            logging.exception("[Mid-Month Task] ERROR during execution.")


# --- 定期実行タスク（月次最終版）---
async def mthAwdLoop(bot: MyBot) -> None:
    """
    月初 0:00 JST に前月分の最終表彰リストを投稿するタスク。
    途中経過と同様、男女別 2 Embed を出力するように修正。
    """
    await bot.wait_until_ready()
    logging.info("[Monthly Award Task] Started.")

    while not bot.is_closed():
        now_jst = TimeMgr.now_jst()

        # ── 次の月初 0:00 (JST) を計算 ──
        next_month_day1 = (now_jst.replace(day=1) + timedelta(days=32)).replace(day=1)
        next_run_dt = datetime.combine(next_month_day1, time(0, 0, 0, tzinfo=TimeMgr.JST))
        wait_seconds = (next_run_dt - now_jst).total_seconds()
        logging.info(f"[Monthly Award Task] Next run at {next_run_dt.isoformat()}  (sleep {wait_seconds:.0f}s)")
        if wait_seconds > 0:
            await asyncio.sleep(wait_seconds)

        # ── 実行時刻ずれチェック ──
        current_jst = TimeMgr.now_jst()
        if abs((current_jst - next_run_dt).total_seconds()) > 60:
            logging.warning("[Monthly Award Task] Skipped due to time drift.")
            continue

        logging.info("[Monthly Award Task] Executing...")
        guild = bot.get_guild(GUILD_ID)
        target_channel = guild.get_channel(TEST_CHANNEL_ID) if guild else None
        if not guild or not bot.db or not isinstance(target_channel, discord.TextChannel):
            logging.error("[Monthly Award Task] Guild/DB/Channel not ready.")
            await asyncio.sleep(60)
            continue

        # 集計対象は「前月」
        prev_month_last = next_run_dt - timedelta(seconds=1)  # JST で前月末 23:59:59
        year, month = prev_month_last.year, prev_month_last.month
        until_utc = next_run_dt.astimezone(TimeMgr.UTC)  # 前月分を完全に締める

        try:
            awards = await AwardCalc.calcMonthly(bot, year, month, guild, until=until_utc)
            if not awards:
                logging.error("[Monthly Award Task] Awards calc returned empty.")
                await asyncio.sleep(60)
                continue

            history = await AwardCalc.getAwardHist(bot, guild)

            # ★★★ 男女別 2 Embed を生成・送信 ★★★
            male_embed, female_embed = AwardCalc.mkAwardEmbeds(
                awards, year, month, history, admin_view=False
            )
            await target_channel.send(embed=male_embed)
            await target_channel.send(embed=female_embed)
            logging.info(f"[Monthly Award Task] Sent male & female embeds for {year}-{month} to {target_channel.id}.")

            # 履歴保存
            await AwardCalc.saveMonthlyHist(bot, awards, guild.id, year, month)
            logging.info(f"[Monthly Award Task] History saved for {year}-{month}.")

        except Exception:
            logging.exception(f"[Monthly Award Task] Error during execution for {year}-{month}.")

        # 少し待機してから次ループへ
        await asyncio.sleep(60)


# --- Botイベント ---
intents = discord.Intents.default();
intents.message_content = True;
intents.voice_states = True;
intents.guilds = True;
intents.members = True
bot = MyBot(command_prefix="$unused$", intents=intents)


@bot.event
async def on_message(message: discord.Message):
    if message.author.bot or not message.guild: return
    if message.channel.id in PROFILE_CHANNELS: await recProfSub(bot, message.author.id, message.created_at)


@bot.event
async def on_voice_state_update(member: discord.Member, before: discord.VoiceState, after: discord.VoiceState):
    if member.id != bot.user.id: await VoiceSess.update_voice_sessions(bot, member, before, after)


@bot.event
async def on_member_update(before: discord.Member, after: discord.Member): pass


@bot.event
async def on_ready():
    logging.info(f"Logged in as {bot.user} (ID: {bot.user.id})")
    logging.info(f"Connected to {len(bot.guilds)} guilds.")
    await updProfSubs(bot)
    logging.info("Bot is fully ready and operational.")


async def updProfSubs(bot: MyBot) -> None:
    logging.info("Updating profile submission log from channels...")
    count = 0;
    processed_users = set()
    if not bot.db: logging.warning("DB not available for updProfSubs."); return
    after_limit = TimeMgr.now_utc() - timedelta(days=30)
    for channel_id in PROFILE_CHANNELS:
        channel = bot.get_channel(channel_id)
        if not isinstance(channel, discord.TextChannel): logging.warning(
            f"Profile channel {channel_id} not found or not text."); continue
        try:
            async for message in channel.history(limit=None, after=after_limit, oldest_first=True):
                if message.author.bot or message.author.id in processed_users: continue
                await recProfSub(bot, message.author.id, message.created_at)
                processed_users.add(message.author.id);
                count += 1
                if count % 100 == 0: await asyncio.sleep(0.1)
        except discord.Forbidden:
            logging.error(f"Missing permissions for history in {channel_id}.")
        except Exception:
            logging.exception(f"Error processing profile channel {channel_id}.")
    logging.info(
        f"Profile submission log update complete. Processed {count} potential subs for {len(processed_users)} users.")


# --- Bot実行 ---
if __name__ == "__main__":
    if not TOKEN:
        print("エラー: 環境変数 DISCORD_BOT_TOKEN が設定されていません。")
    else:
        try:
            bot.run(TOKEN)
        except discord.LoginFailure:
            logging.error("Failed to log in: Invalid token.")
        except Exception:
            logging.exception("An error occurred while running the bot.")
