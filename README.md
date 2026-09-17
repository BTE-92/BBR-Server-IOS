This lets you play Big Bang Racing (by Traplight) on a local Server.

How it works: this runs a server on your PC that pretends to be
the game's original server.



## REQUIREMENTS

* The Big Bang Racing game
* A PC with Python 3 [Click this to download it (32 bit)](https://www.python.org/downloads)
* Git for Windows [Click this to download it (32 bit)](https://git-scm.com/downloads)
* Both devices connected to the same Wi-Fi network


## SETUP - NO JAILBREAK

1. Sideload Big Bang Racing onto your iOS device.

1. Run "BBRServer.bat".

   IMPORTANT: it must be run as Administrator (Windows) or with sudo
   (macOS/Linux). The script needs ports 80, 443 and 53.

   The very first time it runs, it automatically generates its own local
   certificate authority and HTTPS certificate next to the script.

1. Once running, the script prints your PC's local IP address (looks like
   "192.168.1.xxx"). Keep this window open the whole time you play.

1. Install the server's Root CA on your iOS device

   Open it on the device. Go to Settings, you'll see "Profile Downloaded" at the top, tap Install.
   
   Go to Settings > General > About > Certificate Trust Settings, and enable full trust for "BigBangRacing Offline Root CA".

1. Reboot your device.

1. On your device's Wi-Fi settings, tap the (i) next to your network > DNS >
   switch to Manual > set your PC's local IP.

1. Make sure your PC and iOS device are still on the same Wi-Fi network, and
   that the script is still running on the PC.

1. Launch the game.


## SETUP - JAILBREAK



1. Sideload Big Bang Racing onto your iOS device.

1. Run "BBRServer.bat".

   IMPORTANT: it must be run as Administrator (Windows) or with sudo
   (macOS/Linux). The script needs ports 80, 443 and 53.

   The very first time it runs, it automatically generates its own local
   certificate authority and HTTPS certificate next to the script.

1. Once running, the script prints your PC's local IP address (looks like
   "192.168.1.xxx"). Keep this window open the whole time you play.

1. Install the server's Root CA on your iOS device

Open it on the device. Go to Settings, you'll see "Profile Downloaded" at the top, tap Install.

Go to Settings > General > About > Certificate Trust Settings, and enable full trust for "BigBangRacing Offline Root CA".

1. On your device, open your file manager (iFile or Filza), go to the root of
   the filesystem, then into the `etc` folder, and open the `hosts` file with
   the text editor.

1. Tap Edit, and add these lines at the very end (replacing `YOUR_PC_IP` with
   your PC's local IP) :

   ```
   YOUR_PC_IP woeprod.traplightgames.com
   YOUR_PC_IP woeprod-1324136205.us-west-1.elb.amazonaws.com
   YOUR_PC_IP graph.facebook.com
   ```

1. Save, then fully restart your device.

1. Make sure your PC and iOS device are still on the same Wi-Fi network, and
   that the script is still running on the PC.

1. Launch the game.


## TROUBLESHOOTING

* Stuck on "connecting to server" forever: your PC's firewall is probably
  blocking the connection. Try temporarily disabling it to confirm.

* Port 80/443 already in use / IIS: on Windows, IIS (a built-in web server)
  also uses port 80 by default and can conflict with the script. Disable it
  via Win+R > type "optionalfeatures" > uncheck "Internet Information
  Services".

* "OpenSSL was not found on PATH": install Git for Windows

* Game still not connecting even after the DNS change: double check the
  Root CA was actually installed AND trusted (both steps in step 4 above -
  it's easy to install the profile and forget to flip on Certificate Trust
  Settings, in which case the device will silently reject the connection).

* For the DNS Method users, remember to switch your device's DNS back to Automatic when you're not playing, or it
  will lose internet access whenever the script isn't running on your PC.


## SAVING YOUR DATA

Everything (players, levels, scores, ghosts, tournaments, news feed, etc.) is
stored on your PC in a single database file, `game.db`, created next to the
script. You may also see `game.db-wal` and `game.db-shm` appear alongside it -
these are normal SQLite working files, not extra data, and can be ignored. As
long as you keep all of these next to the script and reuse it, everything is
still there next time. Just don't delete them.


## CONTACT

Contact me @baptistewi92 on Discord
