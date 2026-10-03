package core;

import java.util.Set;

public final class WellKnownExtensions{
  private WellKnownExtensions(){}
  public static final Set<String> all= Set.of("""
    123 32x 3ds 3dsx 3g2 3ga 3gp 3gp2 3gpp 3gpp2 3mf 602 669 7z a a26 a78 aa aac aax aaxc abw ac3
    accda accdb accde accdr accdt ace acm adb ade adf adm adml admx adp ads adts afm ag agb ai aif
    aifc aiff aiffc al alz amr amz ani anx ape apk apng appimage appinstaller application appx
    appxbundle ar arj arw as asar asc asd asf asp ass astc asx atom au automount avf avhd avhdx avi
    avif avifs aw awb awk ax axa axv azw3 bak bas bat bcpio bdf bdm bdmv bib bik bk2 blend blender
    blg blp bmp bps brk bsdiff bz bz2 bz3 c cab cap cat cb7 cbl cbor cbr cbt cbz cc cci ccmx cdf cdi
    cdr cdxml cer cert cfg cgb cgm chd chm chrt cl class clpi cls cmake cmd cnt cob coffee com
    config contact cpi cpio cpl cpp cr cr2 cr3 crdownload crl crt crw cs csh cso csproj csr css csv
    csvs cue cur cwk cxx d dar dart dat dbf dbk dcl dcm dcr dds deb der deskthemepack desktop device
    dff di dia diagcab diagcfg diagpkg dib dif diff divx djv djvu dll dmg dmp dng doc docbook docm
    docx dot dotm dotx drl drv dsf dsl dsn dtb dtd dts dtshd dtsi dtx dv dvi dwg dxf e efi egon eif
    el emf eml emp ent eps epsf epsi epub eris erl es escn esd etheme etl etx evt evtx ex exe exp
    exr exs ez f f4a f4b f4v f90 f95 fasl fb2 fd fds fear feature ffu fig fish fit fits fl flac
    flatpak flatpakref flatpakrepo flc fli flv flw fm fnt fo fodg fodp fods fodt fon for fsproj fts
    fxm fxp g3 gadget gb gba gbc gbr gbrjob gcode gcrd gd gdi gdshader ged gedcom gem gen geojson gf
    gg gif gih glade glb gltf gml gmo gnc gnd gnucash gnumeric gnuplot go gp gpg gplt gpx gra gradle
    groovy group grp gs gsf gsh gsm gtar gv gvp gvy gx gy gz h h4 h5 hdf hdf4 hdf5 hdmp hdp heic
    heif hfe hh hif hlp home hp hpgl hpj hpp hqx hs hta htc htm html hwp hwt hxx ica icb icc icl icm
    icns ico ics idl ief iff iges igs ilbm ime img imy inf ini ins inx ips iptables ipynb iqy iso
    iso9660 isp it it87 its j2c j2k jad jar java jceks jfif jks jl jng jnlp jp2 jpc jpe jpeg jpf jpg
    jpg2 jpgm jpm jpr jpx jrd js jse jsm json json5 jsonld jxl jxr k25 k7 kar karbon kdc kdelnk kexi
    kexic kexis key kfo kfx kil kino kml kmz kon kpm kpr kpt kra krz ks ksp ksy kt ktx ktx2 kud kwd
    kwt la latex lbm ldif lha lhs lhz lib lisp lmdb lnk lnx loas log lrv lrz ltx lua lwo lwob lwp
    lws ly lyx lz lz4 lzh lzma lzo m m15 m1u m2t m2ts m3u m3u8 m4 m4a m4b m4r m4u m4v m7 mab mad maf
    mag mak mam man manifest maq mar markdown mas mat mav maw mbox mc2 md mda mdb mde mdi mdmp mdw
    mdx mdz me med meta4 metalink mfl mgp mht mhtml mid midi mif minipsf mj2 mjp2 mjpeg mjpg mjs mk
    mk3d mka mkd mkv ml mli mm mmf mml mng mo mo3 mobi moc mod mof moov mount mov movie mp2 mp3 mp4
    mpc mpe mpeg mpg mpga mpl mpls mpp mpt mrl mrml mrpack mrw ms msc msg msh msh1 msh1xml msh2
    msh2xml mshxml msi msix msixbundle msod msp msstyles mst msu msx mtl mtm mts mui mup mxf mxmf
    mxu n64 nb nc nds nef nes nez nfo ngc ngp nim nimble nims nls not nrw nsc nsv nu numbers nws nzb
    o obj ocl ocx oda odb odc odf odg odi odm odp ods odt oft oga ogg ogm ogv ogx olb old oleo one
    onepkg onetoc2 ooc openvpn opml oprc opus ora orf org ost otc otf otg oth otp ots ott ova ovpn
    owl owx oxps oxt p p10 p12 p65 p7b p7c p7m p7r p7s p8 p8e pack pages pak par2 part pas pat patch
    path pbm pcap pcd pce pcf pcl pct pcx pdb pdc pdf pef pem perl pfa pfb pfr pfx pgm pgn pgp php
    php3 php4 php5 phps pict pict1 pict2 pif pk pkcs8 pkg pkipath pkpass pkr pl pla plg pln pls pm
    pm6 pmd pnf png pnm pntg po pod pol por pot potm potx ppa ppam ppd ppm pps ppsm ppsx ppt pptm
    pptx ppz pqa prc prf prg prn props ps ps1 ps1xml ps2 ps2xml psc1 psc2 psd psd1 psf psflib psid
    psm1 pssc pst psw pub pw py py3 py3x pyc pyi pyo pys pysu pyx qcow qcow2 qd qed qif qml
    qmlproject qmltypes qoi qp qs qt qti qtif qtl qtvr ra raf ram raml rar ras raw rax rb rdf rdfs
    rdg rdp reg rej res resx rgb rle rll rm rmj rmm rms rmvb rmx rnc rng roff ros rp rpm rqy rs rss
    rst rt rtf rtx rv rvx rw2 s3m sage sam sami sap sass sav sc scala scf scm scn scope scr scss sct
    sda sdb sdc sdd sdp sds sdw service settings sfc sg sgb sgd sgf sgi sgl sgm sgml sh shape shar
    shb shn shs siag sid sieve sig sik sis sisx sit sitx siv sk sk1 skr sldm sldx slice slk sln smaf
    smc smd smf smi smil smk sml sms snap snd so socket spc spd spec spkac spl spm spx sql sqlite2
    sqlite3 sqsh sr2 src srf srt srx ss ssa sst stc std sti stl stm stw sty sub sun suo sv sv4cpio
    sv4crc svg svgz svh swap swf swm sxc sxd sxg sxi sxm sxw sylk sys syscap t t2t tak tar target
    targets taz tb2 tbz tbz2 tbz3 tcl tex texi texinfo tga tgz theme themepack thmx tif tiff timer
    tk tlb tlrz tlz tmp tmx tnef tnf toc toml torrent tpic tr tres trig ts tscn tsp tsv tsx tta ttc
    ttf ttl ttx twig txt txz typ tzo tzst udeb udl ufraw ui uil ult unf uni unif url ustar uue v v64
    vala vapi vb vbe vbproj vbs vcard vcf vcs vct vcxproj vda vdi vhd vhdl vhdx viv vivo vlc vmcx
    vmdk vmrs vob voc vor vpc vrm vrml vsd vsdm vsdx vsmacros vss vssm vssx vst vstm vstx vsw vtt
    wab wad wasm wav wax wb1 wb2 wb3 wbk wbmp wcm wdb wdp webm webp website wer wim wk1 wk3 wk4
    wkdownload wks wma wmd wmf wml wmls wmv wmx wmz woff woff2 wp wp4 wp5 wp6 wpd wpg wpl wpp wps
    wri wrl ws wsb wsc wsf wsgi wsh wv wvc wvp wvx wwf x3f xac xar xbap xbel xbl xbm xcf xdgapp xhe
    xht xhtml xi xla xlam xlc xld xlf xliff xll xlm xlr xls xlsb xlsm xlsx xlt xltm xltx xlw xm xmf
    xmi xml xnk xpi xpm xps xsd xsl xslfo xslt xspf xul xwd xz yaml yml yt z z64 zabw zim zip zipx
    zoo zpaq zsav zst zz
    """.split("\\s+"));
}
