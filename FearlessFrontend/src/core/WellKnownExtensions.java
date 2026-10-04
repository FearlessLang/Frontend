package core;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public final class WellKnownExtensions{
  private WellKnownExtensions(){}
  public static final Set<String> all= Set.of("""
    123 32x 3ds 3dsx 3g2 3ga 3gp 3gp2 3gpp 3gpp2 3mf 602 669 7z a a26 a78 aa aac aax aaxc abw ac3
    accda accdb accde accdr accdt ace acm adb ade adf adm adml admx adp ads adts afm ag agb ai aif
    aifc aiff aiffc al alz amr amz ani anx ape apk apng appimage appinstaller application appx
    appxbundle ar args arj arw as asar asc asd asf asp ass astc asx atom au automount avf avhd avhdx avi
    avif avifs aw awb awk ax axa axv azw3 bak bas bat bcpio bdf bdm bdmv bib bik bk2 blend blender
    blg blp bmp bps brk bsdiff built bz bz2 bz3 c cab cap cat cb7 cbl cbor cbr cbt cbz cc cci ccmx cdf cdi
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
    icns ico ics idl ief iff iges igs ilbm ime img imy inf info ini ins inx ips iptables ipynb iqy iso
    iso9660 isp it it87 its j2c j2k jad jar java jceks jfif jks jl jng jnlp jp2 jpc jpe jpeg jpf jpg
    jpg2 jpgm jpm jpr jpx jrd js jse jsm json json5 jsonld jxl jxr k25 k7 kar karbon kdc kdelnk kexi
    kexic kexis key kfo kfx kil kino kml kmz kon kpm kpr kpt kra krz ks ksp ksy kt ktx ktx2 kud kwd
    kwt la latex lbm ldif lha lhs lhz lib lisp lmdb lnk lnx loas lock log lrv lrz ltx lua lwo lwob lwp
    lws ly lyx lz lz4 lzh lzma lzo m m15 m1u m2t m2ts m3u m3u8 m4 m4a m4b m4r m4u m4v m7 mab mad maf
    mag mains mak mam man manifest maq mar markdown mas mat mav maw mbox mc2 md mda mdb mde mdi mdmp mdw
    mdx mdz me med meta4 metalink mfl mgp mht mhtml mid midi mif minipsf mj2 mjp2 mjpeg mjpg mjs mk
    mk3d mka mkd mkv ml mli mm mmf mml mng mo mo3 mobi moc mod mof moov mount mov movie mp2 mp3 mp4
    mpc mpe mpeg mpg mpga mpl mpls mpp mpt mrl mrml mrpack mrw ms msc msg msh msh1 msh1xml msh2
    msh2xml mshxml msi msix msixbundle msod msp msstyles mst msu msx mtl mtm mts mui mup mxf mxmf
    mxu n64 nb nc nds nef nes nez nfo ngc ngp nim nimble nims nls not nrw nsc nsv nu numbers nws nzb
    o obj ocl ocx oda odb odc odf odg odi odm odp ods odt oft oga ogg ogm ogv ogx olb old oleo one
    onepkg onetoc2 ooc openvpn opml oprc opus ora orf org ost otc otf otg oth otp ots ott out ova ovpn
    owl owx oxps oxt p p10 p12 p65 p7b p7c p7m p7r p7s p8 p8e pack pages pak par2 part pas pat patch
    path pbm pcap pcd pce pcf pcl pct pcx pdb pdc pdf pef pem perl pfa pfb pfr pfx pgm pgn pgp php
    php3 php4 php5 phps pict pict1 pict2 pif pk pkcs8 pkg pkipath pkpass pkr pl pla plg pln pls pm
    pm6 pmd pnf png pnm pntg po pod pol por pot potm potx ppa ppam ppd ppm pps ppsm ppsx ppt pptm
    pptx ppz pqa prc prf prg prn properties props ps ps1 ps1xml ps2 ps2xml psc1 psc2 psd psd1 psf psflib psid
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
  public static boolean isWellKnown(String ext){ return all.contains(ext) || ext.matches("ffile[0-9]{3}"); }
  public record Kind(List<String> types, List<String> exts){}
  public static final Map<String,Kind> groups= kinds("""
    application/vnd.lotus-1-2-3 123 wk1 wk3 wk4
    application/x-genesis-32x-rom 32x mdx
    video/3gpp2 3g2 3gp2 3gpp2
    video/3gpp 3ga 3gp 3gpp
    audio/x-mod 669 m15 med mod mtm ult uni
    application/x-archive a ar
    audio/aac aac adts
    application/x-abiword abw zabw
    text/x-adasrc adb ads
    application/x-gba-rom agb gba
    audio/x-aiff aif aiff
    audio/x-aifc aifc aiffc
    application/x-perl al perl pl pod
    text/plain asc txt
    text/x-common-lisp asd fasl lisp ros
    text/x-ssa ass ssa
    audio/x-ms-asx asx wax wmx wvx
    audio/basic au snd
    text/x-systemd-unit automount device mount path scope slice socket swap target timer
    video/vnd.avi avf avi divx
    image/avif avif avifs
    application/vnd.amazon.mobi8-ebook azw3 kfx
    application/x-trash bak old sik
    video/mp2t bdm bdmv clpi cpi m2t m2ts mpls mts
    video/vnd.radgamettools.bink bik bk2
    application/x-blender blend blender
    image/bmp bmp dib
    text/x-c++src text/x-csrc c cc cpp cxx
    application/vnd.tcpdump.pcap cap dmp pcap
    text/x-cobol cbl cob
    application/x-netcdf cdf nc
    application/pkix-cert cer cert crt
    application/x-gameboy-color-rom cgb gbc
    text/x-tex cls dtx ins latex ltx sty tex
    application/x-msdownload cpl dll drv exe scr
    application/x-partial-download crdownload part wkdownload
    application/pkcs10 csr p10
    text/x-dsrc d di
    application/x-docbook+xml dbk docbook
    application/vnd.debian.binary-package deb udeb
    application/x-pem-file application/x-x509-ca-cert der pem
    application/x-desktop desktop kdelnk
    text/x-patch diff patch
    image/vnd.djvu image/vnd.djvu+multipage djv djvu
    text/x-eiffel e eif
    application/vnd.microsoft.portable-executable efi lib ocx sys
    image/x-eps eps epsf epsi
    application/x-godot-scene escn scn tscn
    text/x-elixir ex exs
    text/x-fortran f f90 f95 for
    audio/mp4 f4a m4a
    audio/x-m4b f4b m4b
    video/mp4 f4v lrv m4v mp4
    application/x-raw-floppy-disk-image fd qd
    application/fits fit fits fts
    application/vnd.flatpak flatpak xdgapp
    video/x-flic flc fli
    text/x-xslfo fo xslfo
    application/x-gameboy-rom gb sgb
    text/vcard gcrd vcard vcf vct
    text/vnd.familysearch.gedcom ged gedcom
    application/x-tar gem gtar tar
    application/x-genesis-rom gen sgd
    application/x-gnucash gnc gnucash xac
    application/x-gnuplot gnuplot gp gplt
    application/pgp-encrypted application/pgp-keys application/pgp-signature gpg pgp pkr sig skr
    text/x-groovy groovy gsh gvy gy
    application/x-font-type1 gsf pfa pfb
    application/x-hdf h4 h5 hdf hdf4 hdf5
    image/jxr hdp jxr wdp
    image/heif heic heif hif
    text/x-c++hdr hh hp hpp hxx
    text/html htm html
    image/x-tga icb tga tpic vda
    application/vnd.iccprofile icc icm
    text/calendar ics vcs
    image/x-ilbm iff ilbm lbm
    model/iges iges igs
    text/x-iMelody ime imy
    application/vnd.efi.iso iso iso9660
    image/x-jp2-codestream j2c j2k jpc
    image/jpeg jfif jpe jpeg jpg
    application/x-java-keystore jks ks
    image/jp2 jp2 jpg2
    image/jpm jpgm jpm
    text/javascript js jsm mjs
    audio/midi kar mid midi
    application/smil+xml kino smil sml
    application/x-kpresenter kpr kpt
    application/x-krita kra krz
    application/x-kword kwd kwt
    application/x-lha lha lzh
    audio/usac loas xhe
    image/x-lwo lwo lwob
    video/vnd.mpegurl m1u m4u mxu
    application/vnd.apple.mpegurl audio/x-mpegurl m3u m3u8 vlc
    text/x-makefile mak mk
    text/markdown markdown md mkd
    application/x-mimearchive mht mhtml
    video/mj2 mj2 mjp2
    video/x-mjpeg mjpeg mjpg
    text/x-ocaml ml mli
    application/vnd.smaf mmf smaf
    video/quicktime moov mov qt qtvr
    audio/mpeg mp3 mpga
    audio/x-musepack mpc mpp
    video/mpeg mpe mpeg mpg vob
    text/x-mrml mrl mrml
    text/x-mup mup not
    application/x-n64-rom n64 v64 z64
    application/x-nes-rom nes nez unf unif
    text/x-nimscript nimble nims
    audio/ogg audio/x-flac+ogg audio/x-opus+ogg audio/x-speex audio/x-speex+ogg audio/x-vorbis+ogg video/ogg video/x-theora+ogg oga ogg ogv opus spx
    application/x-openvpn-profile openvpn ovpn
    application/vnd.palm oprc pqa
    application/rdf+xml owl rdf rdfs
    text/x-pascal p pas
    application/x-pkcs12 p12 pfx
    application/x-pagemaker p65 pm6 pmd
    application/pkcs7-mime application/x-pkcs7-certificates p7b p7c p7m spc
    application/pkcs8 p8 pkcs8
    image/x-pict pct pict pict1 pict2
    application/x-php php php3 php4 php5 phps
    application/x-xar pkg xar
    application/vnd.ms-powerpoint pps ppt ppz
    audio/prs.sid psid sid
    text/x-python py pyx wsgi
    text/x-python3 py3 py3x pyi
    application/x-python-bytecode pyc pyo
    application/x-qemu-disk qcow qcow2
    text/x-qml qml qmlproject qmltypes
    audio/vnd.rn-realaudio ra rax
    application/x-godot-resource res tres
    application/vnd.rn-realmedia rm rmj rmm rms rmvb rmx
    application/xml rng xbl xml xsd
    text/troff roff tr
    video/vnd.rn-realvideo rv rvx
    application/x-spss-sav sav zsav
    text/x-scala sc scala
    text/x-scheme scm ss
    application/vnd.stardivision.writer sdw sgl vor
    application/vnd.nintendo.snes.rom sfc smc
    text/sgml sgm sgml
    application/sieve sieve siv
    image/x-skencil sk sk1
    text/spreadsheet slk sylk
    application/vnd.adobe.flash.movie spl swf
    application/x-ms-wim swm wim
    application/x-bzip2-compressed-tar tb2 tbz2
    text/tcl tcl tk
    text/x-texinfo texi texinfo
    image/tiff tif tiff
    application/vnd.ms-tnef tnef tnf
    text/x-vala vala vapi
    video/vnd.vivo viv vivo
    model/vrml vrm vrml wrl
    application/vnd.visio vsd vss vsw
    application/x-quattropro wb1 wb2 wb3
    application/vnd.ms-works wcm wdb wps xlr
    application/vnd.wordperfect wp wp4 wp5 wp6 wpd wpp
    audio/x-wavpack wv wvp
    application/xhtml+xml xht xhtml
    application/vnd.ms-excel xla xlc xld xll xlm xls xlt xlw
    application/xliff+xml xlf xliff
    application/xslt+xml xsl xslt
    application/yaml yaml yml
    application/zip zip zipx
    """);
  public static final Map<String,Kind> unclaimable= kinds("""
    application/x-nintendo-3ds-rom image/x-3ds 3ds
    application/msword-template text/vnd.graphviz dot
    audio/vnd.dts text/x-devicetree-source dts
    application/vnd.gerber image/x-gimp-gbr gbr
    application/x-jbuilder-project image/jpx jpx
    text/x-matlab text/x-objcsrc m
    text/x-objc++src text/x-troff-mm mm
    application/x-gettext-translation text/x-modelica mo
    audio/mp2 video/mpeg mp2
    text/x-mpl2 video/mp2t mpl
    application/x-tgif model/obj obj
    application/vnd.oasis.opendocument.formula-template font/otf otf
    application/x-cisco-vpn-settings application/x-font-pcf pcf
    application/x-ms-pdb chemical/x-pdb pdb
    application/x-pagemaker application/x-perl pm
    application/vnd.ms-powerpoint text/x-gettext-translation-template pot
    application/vnd.palm application/x-mobipocket-ebook prc
    application/x-font-linux-psf audio/x-psf psf
    application/x-qw image/x-quicktime qif
    application/sdp application/vnd.stardivision.impress sdp
    text/x-dbus-service text/x-systemd-unit service
    application/vnd.stardivision.mail application/x-genesis-rom smd
    application/smil+xml application/x-sami smi
    application/x-perl text/troff t
    text/vnd.trolltech.linguist video/mp2t ts
    application/x-designer application/x-gtk-builder ui
    application/x-virtual-boy-rom text/x-vb vb
    application/x-vhd-disk text/x-vhdl vhd
    application/vnd.visio image/x-tga vst
    application/vnd.lotus-1-2-3 application/vnd.ms-works wks
    """);
  private static Map<String,Kind> kinds(String text){
    return text.lines().map(WellKnownExtensions::kind)
      .flatMap(k->k.exts().stream().map(e->Map.entry(e,k)))
      .collect(Collectors.toUnmodifiableMap(Map.Entry::getKey,Map.Entry::getValue));
  }
  private static Kind kind(String line){
    var ws= Stream.of(line.split(" ")).collect(Collectors.partitioningBy(w->w.contains("/")));
    return new Kind(List.copyOf(ws.get(true)),List.copyOf(ws.get(false)));
  }
}
