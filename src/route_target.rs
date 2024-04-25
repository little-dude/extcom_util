/// A route target extended community as defined in [RFC4360 section 4]
///
/// [RFC4360 section 4]: https://www.rfc-editor.org/rfc/rfc4360#section-4
///
/// # Examples
///
/// ```rust
/// # use std::str::FromStr;
/// # use extcom_util::RouteTarget;
/// // A two-octets ASN route target (aka type 0)
/// let rt = "1:2".parse::<RouteTarget>().unwrap();
/// // It can also be created from an integer
/// assert_eq!(RouteTarget::try_from(0x0002_0001_0000_0002).unwrap(), rt);
///
/// // Route targets are transitive
/// assert!(rt.is_transitive());
/// // The type high octet shouldn't have the authority bit set
/// assert!(!rt.type_high().iana_authority());
///
/// // Display and debug representations
/// assert_eq!(rt.to_string(), "1:2");
/// assert_eq!(format!("{:?}", rt), "RouteTarget(1:2 (type high: 0x00, type low: 0x02, global administrator: 1, local administrator 2))");
///
/// // The display implementation differs for each type of route target
/// // Two bytes ASN (aka type 0)
/// let type0 = "111:222".parse::<RouteTarget>().unwrap();
/// assert_eq!(type0.to_string(), "111:222");
/// assert_eq!(format!("{:?}", type0), "RouteTarget(111:222 (type high: 0x00, type low: 0x02, global administrator: 111, local administrator 222))");
/// // IPv4 address (aka type 1)
/// let type1 = "1.2.3.4:333".parse::<RouteTarget>().unwrap();
/// assert_eq!(type1.to_string(), "1.2.3.4:333");
/// assert_eq!(format!("{:?}", type1), "RouteTarget(1.2.3.4:333 (type high: 0x01, type low: 0x02, global administrator: 16909060, local administrator 333))");
/// // Four bytes ASN (aka type 2)
/// let type2 = "111.222:333".parse::<RouteTarget>().unwrap();
/// assert_eq!(type2.to_string(), "111.222:333");
/// assert_eq!(format!("{:?}", type2), "RouteTarget(111.222:333 (type high: 0x02, type low: 0x02, global administrator: 7274718, local administrator 333))");
/// ```
///
/// The `FromStr` implementation is quite flexible
///
/// It ignores some prefixes like `rt`, `route-target` or `target`:
/// ```rust
/// # use std::str::FromStr;
/// # use extcom_util::RouteTarget;
/// let rt1 = "111:222".parse::<RouteTarget>().unwrap();
/// let rt2 = "rt:111:222".parse::<RouteTarget>().unwrap();
/// let rt3 = "route-target:111:222".parse::<RouteTarget>().unwrap();
/// let rt4 = "111:222".parse::<RouteTarget>().unwrap();
///
/// assert_eq!(rt1, rt2);
/// assert_eq!(rt1, rt3);
/// assert_eq!(rt1, rt4);
/// ```
///
/// The type can be omitted if the global administrator field is
/// formatted using a non-ambiguous syntax:
///
/// ```
/// # use std::str::FromStr;
/// # use extcom_util::RouteTarget;
/// // Assumed to be of type 0 since global administrator is a decimal number
/// let _ = "111:222".parse::<RouteTarget>().unwrap();
/// // Assumed to be of type 1 since global administrator is an IPv4 address
/// let _ = "1.1.1.1:222".parse::<RouteTarget>().unwrap();
/// // Assumed to be of type 1 since global administrator uses dotted ASN4 notation
/// let _ = "123.123:222".parse::<RouteTarget>().unwrap();
/// ```
///
/// Otherwise, the type field must be specified as a decimal number:
///
/// ```
/// # use std::str::FromStr;
/// # use extcom_util::RouteTarget;
/// assert_eq!(
///     // type high = 0x00, type low = 0x02, so type field is 0x0002 = 2
///     "2:111:222".parse::<RouteTarget>().unwrap(),
///     "111:222".parse::<RouteTarget>().unwrap(),
/// );
///
/// assert_eq!(
///     // type high = 0x01, type low = 0x02, so type field is 0x0102 = 258
///     "258:16843009:222".parse::<RouteTarget>().unwrap(),
///     "1.1.1.1:222".parse::<RouteTarget>().unwrap(),
/// );
///
/// assert_eq!(
///     // type high = 0x02, type low = 0x02, so type field is 0x0202 = 514
///     "514:8061051:222".parse::<RouteTarget>().unwrap(),
///     "123.123:222".parse::<RouteTarget>().unwrap(),
/// );
/// ```
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct RouteTarget(GenericExtendedCommunity);

impl RouteTarget {
    /// Format this route target using the given format string.
    ///
    /// The format string controls how the global administrator and
    /// local administrator fields should be displayed. See the examples below
    ///
    /// # Example
    ///
    /// ```rust
    /// # use extcom_util::RouteTarget;
    /// // A two-octets ASN route target (aka type 0)
    /// let rt = "123:1234".parse::<RouteTarget>().unwrap();
    /// // Default representation
    /// assert_eq!(rt.to_string(), "123:1234");
    /// // Debug representation
    /// assert_eq!(
    ///     format!("{:?}", rt),
    ///     "RouteTarget(123:1234 (type high: 0x00, type low: 0x02, global administrator: 123, local administrator 1234))"
    /// );
    /// // <type>:<global admin>:<local admin> all in decimal
    /// assert_eq!(rt.format("%(t):%(g):%(l)").to_string(), "2:123:1234");
    /// // <type (binary)>:<global admin>:<local admin>
    /// assert_eq!(rt.format("%(t,b):%(g):%(l)").to_string(), "0b10:123:1234");
    /// // <type high (binary with padding)>:<type low (binary with padding)>:<global admin>:<local admin>
    /// assert_eq!(rt.format("%(th,!b):%(tl,!b):%(g):%(l)").to_string(), "0b00000000:0b00000010:123:1234");
    /// // As an integer in decimal
    /// assert_eq!(rt.format("%(i,d)").to_string(), "563478234399954");
    ///
    /// // An IPv4 address route target (aka type 1)
    /// let rt = "10.0.0.1:1234".parse::<RouteTarget>().unwrap();
    /// // Default representation
    /// assert_eq!(rt.to_string(), "10.0.0.1:1234");
    /// // Debug representation
    /// assert_eq!(format!("{:?}", rt), "RouteTarget(10.0.0.1:1234 (type high: 0x01, type low: 0x02, global administrator: 167772161, local administrator 1234))");
    /// // As an integer in uppercase hexadecimal with padding
    /// assert_eq!(rt.format("%(i, !X)").to_string(), "0x01020A00000104D2");
    ///
    /// // A four-octets ASN route target (aka type 2)
    /// let rt = "123.456:1234".parse::<RouteTarget>().unwrap();
    /// // Default representation
    /// assert_eq!(rt.to_string(), "123.456:1234");
    /// // Debug representation
    /// assert_eq!(format!("{:?}", rt), "RouteTarget(123.456:1234 (type high: 0x02, type low: 0x02, global administrator: 8061384, local administrator 1234))");
    /// // All hex with padding
    /// let fmt_str = "type_high(%(th,!x)) type_low(%(tl,!x)) global_admin(%(g,!x)) local_admin(%(l,!x))";
    /// assert_eq!(rt.format(fmt_str).to_string(), "type_high(0x02) type_low(0x02) global_admin(0x007b01c8) local_admin(0x04d2)");
    /// // All hex uppercase without padding
    /// let fmt_str = "type_high(%(th,X)) type_low(%(tl,X)) global_admin(%(g,X)) local_admin(%(l,X))";
    /// assert_eq!(rt.format(fmt_str).to_string(), "type_high(0x2) type_low(0x2) global_admin(0x7B01C8) local_admin(0x4D2)");
    /// ```
    pub fn format<'a>(&self, fmt_str: &'a str) -> DelayedRouteTargetFormat<'a> {
        DelayedRouteTargetFormat::new(*self, fmt_str)
    }

    /// Return the global administrator field as a 32 bits integer.
    ///
    /// Depending on the route target format, the global administrator
    /// field may be a 16 bits field, in which case the least
    /// significant 16 bits are all 0.
    pub fn global_administrator(&self) -> u32 {
        self.basic_type_value().global_administrator()
    }

    /// Return the local administrator field as a 32 bits integer.
    ///
    /// Depending on the route target format, the local administrator
    /// field may be a 16 bits field, in which case the most
    /// significant 16 bits are all 0.
    pub fn local_administrator(&self) -> u32 {
        self.basic_type_value().local_administrator()
    }

    pub fn r#type(&self) -> u16 {
        self.0.r#type()
    }

    /// Return the type high octet
    pub fn type_high(&self) -> TypeHigh {
        self.0.type_high()
    }

    /// Whether the transitive bit on the type high octet is set.
    ///
    /// For route targets, this is always true.
    pub fn is_transitive(&self) -> bool {
        self.0.is_transitive()
    }

    /// Return the type low octet
    ///
    /// For route targets, this is always 0x02.
    pub fn type_low(&self) -> u8 {
        self.0.type_low()
    }

    /// Return the basic type value representation of this route
    /// target.
    pub fn basic_type_value(&self) -> BasicTypeValue {
        self.0.basic_type_value().unwrap()
    }

    /// Return the type value representation of this route target.
    ///
    /// For a route target, this is always [`TypeValue::BasicTypeValue`]
    pub fn type_value(&self) -> TypeValue {
        self.basic_type_value().into()
    }

    /// Return this route target as a raw 64 bits integer
    pub fn as_u64(&self) -> u64 {
        self.0.as_u64()
    }
}

impl fmt::Debug for RouteTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format("RouteTarget(%(g):%(l) (type high: %(th,!x), type low: %(tl,!x), global administrator: %(g,d), local administrator %(l,d)))"))
    }
}

/// Error returned when failing to parse a route target string
/// target.
#[derive(Debug, thiserror::Error)]
#[error("invalid route target string \"{}\"", _0)]
pub struct InvalidRouteTargetStr(String);

impl From<BasicTypeValue> for RouteTarget {
    fn from(tv: BasicTypeValue) -> Self {
        let type_high: u8 = match tv {
            BasicTypeValue::TwoOctetAs { .. } => 0x00,
            BasicTypeValue::IPv4Address { .. } => 0x01,
            BasicTypeValue::FourOctetAs { .. } => 0x02,
        };
        let type_low: u8 = 0x02;
        Self(GenericExtendedCommunity::from(
            ((type_high as u64) << 56) | ((type_low as u64) << 48) | tv.raw_value(),
        ))
    }
}

impl FromStr for RouteTarget {
    type Err = InvalidRouteTargetStr;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = if let Some(stripped) = s.strip_prefix("target:") {
            stripped
        } else if let Some(stripped) = s.strip_prefix("route-target:") {
            stripped
        } else if let Some(stripped) = s.strip_prefix("rt:") {
            stripped
        } else {
            s
        };
        let mut parts = s.split(':');
        let part1 = parts
            .next()
            .ok_or_else(|| InvalidRouteTargetStr(s.to_owned()))?;
        let part2 = parts
            .next()
            .ok_or_else(|| InvalidRouteTargetStr(s.to_owned()))?;
        if let Some(part3) = parts.next() {
            parse_three_parts_route_target(part1, part2, part3)
                .ok_or_else(|| InvalidRouteTargetStr(s.to_owned()))
        } else {
            parse_two_parts_route_target(part1, part2)
                .ok_or_else(|| InvalidRouteTargetStr(s.to_owned()))
        }
    }
}

fn parse_three_parts_route_target(
    type_s: &str,
    global_s: &str,
    local_s: &str,
) -> Option<RouteTarget> {
    match type_s.parse::<u16>().ok()? {
        0x0002 => Some(
            BasicTypeValue::TwoOctetAs {
                global_administrator: global_s.parse::<u16>().ok()?,
                local_administrator: local_s.parse::<u32>().ok()?,
            }
            .into(),
        ),
        0x0102 => Some(
            BasicTypeValue::IPv4Address {
                global_administrator: global_s.parse::<u32>().ok()?,
                local_administrator: local_s.parse::<u16>().ok()?,
            }
            .into(),
        ),
        0x0202 => Some(
            BasicTypeValue::FourOctetAs {
                global_administrator: global_s.parse::<u32>().ok()?,
                local_administrator: local_s.parse::<u16>().ok()?,
            }
            .into(),
        ),
        _ => None,
    }
}

fn parse_two_parts_route_target(global_s: &str, local_s: &str) -> Option<RouteTarget> {
    match (global_s.parse::<Ipv4Addr>(), local_s.parse::<u16>()) {
        (Ok(global), Ok(local)) => {
            return Some(
                BasicTypeValue::IPv4Address {
                    global_administrator: global.into(),
                    local_administrator: local,
                }
                .into(),
            );
        }
        (Ok(_), Err(_)) => {
            return None;
        }
        _ => {}
    }

    // Try to parse 666.777:1234
    let mut global_s_parts = global_s.split('.');
    let part1 = global_s_parts.next();
    let part2 = global_s_parts.next();
    let part3 = global_s_parts.next();
    if let (Some(part1), Some(part2), None) = (part1, part2, part3) {
        match (
            part1.parse::<u16>(),
            part2.parse::<u16>(),
            local_s.parse::<u16>(),
        ) {
            (Ok(asn1), Ok(asn2), Ok(local)) => {
                return Some(
                    BasicTypeValue::FourOctetAs {
                        global_administrator: (asn1 as u32) << 16 | asn2 as u32,
                        local_administrator: local,
                    }
                    .into(),
                );
            }
            _ => {
                return None;
            }
        }
    }

    // Try to parse 1234:1234
    match (global_s.parse::<u16>(), local_s.parse::<u32>()) {
        (Ok(global), Ok(local)) => Some(
            BasicTypeValue::TwoOctetAs {
                global_administrator: global,
                local_administrator: local,
            }
            .into(),
        ),
        _ => None,
    }
}

impl fmt::Display for RouteTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format("%(g):%(l)"))
    }
}

/// Error returned when a 64 bits integer doesn't represent a valid route target
#[derive(Debug, thiserror::Error, Clone, Copy)]
#[error(
    "invalid route target: type high: {:#010b}, type low: {:#010b}, raw: {:#018x}",
    type_high,
    type_low,
    raw
)]
pub struct InvalidRouteTarget {
    type_high: u8,
    type_low: u8,
    raw: u64,
}

impl TryFrom<GenericExtendedCommunity> for RouteTarget {
    type Error = InvalidRouteTarget;
    fn try_from(v: GenericExtendedCommunity) -> Result<Self, Self::Error> {
        if v.type_high().as_u8() < 0x03 && v.type_low() == 0x02 {
            Ok(Self(v))
        } else {
            Err(InvalidRouteTarget {
                type_high: v.type_high().into(),
                type_low: v.type_low(),
                raw: v.0,
            })
        }
    }
}

impl TryFrom<u64> for RouteTarget {
    type Error = InvalidRouteTarget;
    fn try_from(v: u64) -> Result<Self, Self::Error> {
        GenericExtendedCommunity::from(v).try_into()
    }
}

impl From<RouteTarget> for GenericExtendedCommunity {
    fn from(v: RouteTarget) -> GenericExtendedCommunity {
        v.0
    }
}

impl From<RouteTarget> for u64 {
    fn from(v: RouteTarget) -> u64 {
        v.0.into()
    }
}

#[derive(Debug)]
pub struct DelayedRouteTargetFormat<'a> {
    rt: RouteTarget,
    items: RouteTargetFmtParser<'a>,
}

impl<'a> DelayedRouteTargetFormat<'a> {
    fn new(rt: RouteTarget, format_str: &'a str) -> Self {
        Self {
            rt,
            items: format_str.into(),
        }
    }
}

impl<'a> fmt::Display for DelayedRouteTargetFormat<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for item in self.items.clone() {
            match item {
                FmtItem::Literal(s) => f.write_str(s)?,
                FmtItem::Item(RouteTargetFmtItem::Int(repr)) => {
                    let int = self.rt.as_u64();
                    match repr {
                        IntFmt::Default | IntFmt::Decimal => {
                            write!(f, "{int}")?;
                        }
                        IntFmt::Hex { padding, uppercase } => {
                            fmt_hex_integer(f, int, FieldSize::U64, uppercase, padding)?;
                        }
                        IntFmt::Bin { padding } => {
                            fmt_bin_integer(f, int, FieldSize::U64, padding)?;
                        }
                    }
                }
                FmtItem::Item(RouteTargetFmtItem::Type(repr)) => {
                    let ty = self.rt.r#type();
                    match repr {
                        IntFmt::Default | IntFmt::Decimal => {
                            write!(f, "{ty}")?;
                        }
                        IntFmt::Hex { padding, uppercase } => {
                            fmt_hex_integer(f, ty as u64, FieldSize::U16, uppercase, padding)?;
                        }
                        IntFmt::Bin { padding } => {
                            fmt_bin_integer(f, ty as u64, FieldSize::U16, padding)?;
                        }
                    }
                }
                FmtItem::Item(RouteTargetFmtItem::TypeLow(repr)) => {
                    let ty = self.rt.type_low();
                    match repr {
                        IntFmt::Decimal => {
                            write!(f, "{ty}")?;
                        }
                        IntFmt::Hex { padding, uppercase } => {
                            fmt_hex_integer(f, ty as u64, FieldSize::U8, uppercase, padding)?;
                        }
                        IntFmt::Default => {
                            fmt_bin_integer(f, ty as u64, FieldSize::U8, true)?;
                        }
                        IntFmt::Bin { padding } => {
                            fmt_bin_integer(f, ty as u64, FieldSize::U8, padding)?;
                        }
                    }
                }
                FmtItem::Item(RouteTargetFmtItem::TypeHigh(repr)) => {
                    let ty = self.rt.type_high().as_u8();
                    match repr {
                        IntFmt::Decimal => {
                            write!(f, "{ty}")?;
                        }
                        IntFmt::Hex { padding, uppercase } => {
                            fmt_hex_integer(f, ty as u64, FieldSize::U8, uppercase, padding)?;
                        }
                        IntFmt::Default => {
                            fmt_bin_integer(f, ty as u64, FieldSize::U8, true)?;
                        }
                        IntFmt::Bin { padding } => {
                            fmt_bin_integer(f, ty as u64, FieldSize::U8, padding)?;
                        }
                    }
                }
                FmtItem::Item(RouteTargetFmtItem::GlobalAdministrator(repr)) => {
                    fmt_btv_item(
                        f,
                        self.rt.basic_type_value(),
                        BasicTypeValueFmtItem::GlobalAdministrator(repr),
                    )?;
                }
                FmtItem::Item(RouteTargetFmtItem::LocalAdministrator(repr)) => {
                    fmt_btv_item(
                        f,
                        self.rt.basic_type_value(),
                        BasicTypeValueFmtItem::LocalAdministrator(repr),
                    )?;
                }
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
enum RouteTargetFmtItem {
    Int(IntFmt),
    Type(IntFmt),
    TypeHigh(IntFmt),
    TypeLow(IntFmt),
    GlobalAdministrator(IntFmt),
    LocalAdministrator(IntFmt),
}

#[derive(Debug, Clone)]
struct RouteTargetFmtParser<'a>(Tokenizer<'a>);

impl<'a, T> From<T> for RouteTargetFmtParser<'a>
where
    T: Into<Tokenizer<'a>>,
{
    fn from(value: T) -> Self {
        Self(value.into())
    }
}

impl<'a> Iterator for RouteTargetFmtParser<'a> {
    type Item = FmtItem<'a, RouteTargetFmtItem>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0.next()? {
            Token::Literal(s) => Some(FmtItem::Literal(s)),
            Token::IntInterpolation { item, repr, raw } => {
                match item {
                    "i" | "I" => Some(RouteTargetFmtItem::Int(repr).into()),
                    "g" | "G" => Some(RouteTargetFmtItem::GlobalAdministrator(repr).into()),
                    "l" | "L" => Some(RouteTargetFmtItem::LocalAdministrator(repr).into()),
                    "t" | "T" => Some(RouteTargetFmtItem::Type(repr).into()),
                    "tl" | "TL" => Some(RouteTargetFmtItem::TypeLow(repr).into()),
                    "th" | "TH" => Some(RouteTargetFmtItem::TypeHigh(repr).into()),
                    // FIXME: we should return an error here
                    _ => Some(FmtItem::Literal(raw)),
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
enum Token<'a> {
    Literal(&'a str),
    IntInterpolation {
        item: &'a str,
        repr: IntFmt,
        raw: &'a str,
    },
}

#[derive(Debug, Clone)]
struct Tokenizer<'a>(&'a str);

impl<'a> From<&'a str> for Tokenizer<'a> {
    fn from(value: &'a str) -> Self {
        Self(value)
    }
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.0.is_empty() {
            return None;
        }
        match self.0.find("%(") {
            Some(0) => match self.0.find(')') {
                Some(index) => {
                    let lit = &self.0[..=index];
                    let token =
                        if let Some((item, repr)) = parse_int_interpolation(&self.0[2..index]) {
                            Token::IntInterpolation {
                                item,
                                repr,
                                raw: lit,
                            }
                        } else {
                            Token::Literal(lit)
                        };
                    self.0 = &self.0[index + 1..];
                    Some(token)
                }
                None => {
                    let token = Token::Literal(self.0);
                    self.0 = &self.0[self.0.len()..];
                    Some(token)
                }
            },
            Some(i) => {
                let token = Token::Literal(&self.0[..i]);
                self.0 = &self.0[i..];
                Some(token)
            }
            None => {
                let token = Token::Literal(self.0);
                self.0 = &self.0[self.0.len()..];
                Some(token)
            }
        }
    }
}

fn parse_int_interpolation(s: &str) -> Option<(&str, IntFmt)> {
    let mut parts = s.split(',').map(|s| s.trim());
    let item = parts.next()?;
    let repr = if let Some(s) = parts.next() {
        let s = s.as_bytes();
        let mut offset = 0;
        let mut padding = false;
        if let Some(b'!') = s.get(offset) {
            padding = true;
            offset = 1;
        }
        let repr = match s.get(offset) {
            Some(b'd' | b'D') => IntFmt::Decimal,
            Some(b'X') => IntFmt::Hex {
                padding,
                uppercase: true,
            },
            Some(b'x') => IntFmt::Hex {
                padding,
                uppercase: false,
            },
            Some(b'b' | b'B') => IntFmt::Bin { padding },
            _ => return None,
        };
        if s.get(offset + 1).is_some() {
            return None;
        }
        repr
    } else {
        IntFmt::Default
    };
    Some((item, repr))
}
