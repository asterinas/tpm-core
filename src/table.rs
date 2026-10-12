use super::handle::*;

/// 上下文表的槽位状态。
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CtxSlot {
    /// 空闲槽位。
    Empty,
    /// 对象内容已保存到备份缓冲区，芯片上无对应句柄。
    Saved,
    /// 槽位持有一个活跃的物理句柄。
    Live(u32),
}
#[derive(Clone, Copy)]
pub struct SpaceTable {
    ctx: [CtxSlot; SLOTS],
    /// `0` 表示空槽。
    sessions: [u32; SLOTS],
}
impl SpaceTable {
    pub fn new() -> Self {
        SpaceTable {
            ctx: [CtxSlot::Empty; SLOTS],
            sessions: [0u32; SLOTS],
        }
    }
}

impl Default for SpaceTable {
    fn default() -> Self {
        Self::new()
    }
}

impl SpaceTable {
    /// 把槽位置为空闲或已保存。这两种状态不携带句柄，永远不破坏不变量。
    pub fn set_slot_free(&mut self, i: usize, saved: bool) {
        self.ctx[i] = if saved {
            CtxSlot::Saved
        } else {
            CtxSlot::Empty
        };
    }
    /// 把槽位置为活跃。要求句柄合法且未被登记过。
    ///
    /// 「未被登记过」是前置条件而不是运行时检查：调用点（`intern`、
    /// 装载路径）本来就已经查过一遍表，再查一次纯属浪费。单射性由此
    /// 条前置条件承接，不引入任何信任假设。
    pub fn set_slot_live(&mut self, i: usize, p: u32) {
        self.ctx[i] = CtxSlot::Live(p);
    }
    /// 虚拟句柄 → 物理句柄。
    pub fn resolve(&self, v: u32) -> Option<u32> {
        if !is_transient_exec(v) {
            return None;
        }
        let i = slot_of_exec(v);
        if i >= SLOTS {
            return None;
        }
        match self.ctx[i] {
            CtxSlot::Live(p) => Some(p),
            _ => None,
        }
    }
    /// 物理句柄 → 虚拟句柄，仅查询，不分配。
    pub fn lookup(&self, p: u32) -> Option<u32> {
        self.ctx
            .iter()
            .position(|&slot| slot == CtxSlot::Live(p))
            .map(vhandle_of_exec)
    }
    /// 为物理句柄分配一个空闲槽位，返回对应虚拟句柄。
    ///
    /// 表满时返回 `None`；此时调用方**有义务**把这个物理句柄在芯片上释放，
    /// 否则它会一直占着芯片资源且再也无法被引用。
    pub fn intern(&mut self, p: u32) -> Option<u32> {
        let i = self.ctx.iter().position(|&slot| slot == CtxSlot::Empty)?;
        self.set_slot_live(i, p);
        Some(vhandle_of_exec(i))
    }
    /// 登记一个会话句柄。表满时返回 `false`，调用方同样负有释放义务。
    pub fn add_session(&mut self, h: u32) -> bool {
        match self.sessions.iter_mut().find(|slot| **slot == 0) {
            Some(slot) => {
                *slot = h;
                true
            }
            None => false,
        }
    }
    pub fn has_session_exec(&self, h: u32) -> bool {
        self.sessions.contains(&h)
    }
    pub fn session_at(&self, i: usize) -> u32 {
        self.sessions[i]
    }
    pub fn clear_session(&mut self, i: usize) {
        self.sessions[i] = 0;
    }
    pub fn slot_at(&self, i: usize) -> CtxSlot {
        self.ctx[i]
    }
}
