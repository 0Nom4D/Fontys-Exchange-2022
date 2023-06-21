import 'package:flutter/material.dart';

import 'package:percent_indicator/circular_percent_indicator.dart';
import 'package:provider/provider.dart';

import 'package:app/src/providers/achievements_provider.dart';
import 'package:app/src/widgets/badge_list.dart';

class ProfileView extends StatefulWidget {
  const ProfileView({super.key});

  @override
  ProfileViewState createState() => ProfileViewState();
}

class ProfileViewState extends State<ProfileView> {
  @override
  Widget build(BuildContext context) {
    AchievementProvider provider = Provider.of<AchievementProvider>(context, listen: false);

    return Scaffold(
      appBar: AppBar(
        automaticallyImplyLeading: false,
        title: const Text(
          "",
          style: TextStyle(
            color: Colors.black,
            fontWeight: FontWeight.bold,
            fontSize: 40,
          )
        ),
        backgroundColor: Colors.transparent,
      ),
      body: Padding(
        padding: const EdgeInsets.symmetric(vertical: 10, horizontal: 15),
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            const Text(
              "Profile",
              textAlign: TextAlign.start,
              style: TextStyle(
                color: Colors.white,
                fontSize: 40,
                fontWeight: FontWeight.bold
              ),
            ),
            const SizedBox(height: 20),
            Row(
              mainAxisAlignment: MainAxisAlignment.spaceEvenly,
              crossAxisAlignment: CrossAxisAlignment.center,
              children: [
                CircularPercentIndicator(
                  radius: 78,
                  lineWidth: 8,
                  percent: provider.achievements.where((element) => !element.isLocked).toList().length / provider.achievements.length,
                  center: const CircleAvatar(
                    radius: 70,
                    backgroundImage: AssetImage("assets/profile.png"),
                  ),
                  progressColor: Colors.green,
                ),
                Column(
                  mainAxisAlignment: MainAxisAlignment.center,
                  crossAxisAlignment: CrossAxisAlignment.start,
                  children: [
                    const Text(
                      "0Nom4D-",
                      textAlign: TextAlign.start,
                      style: TextStyle(
                        color: Colors.white,
                        fontSize: 40,
                        fontWeight: FontWeight.bold
                      ),
                    ),
                    Row(
                      children: [
                        const Icon(Icons.emoji_events, color: Colors.white),
                        const SizedBox(width: 5),
                        Text(
                          "${provider.achievements.where((element) => !element.isLocked).toList().length}/${provider.achievements.length} Badges",
                          style: const TextStyle(
                            fontWeight: FontWeight.bold,
                            fontStyle: FontStyle.italic,
                            color: Colors.white
                          )
                        )
                      ],
                    )
                  ],
                )
              ],
            ),
            const SizedBox(height: 10),
            Align(
              alignment: Alignment.centerRight,
              child: ElevatedButton.icon(
                style: ElevatedButton.styleFrom(
                  backgroundColor: Colors.white.withOpacity(.2),
                  shape: RoundedRectangleBorder(
                    borderRadius: BorderRadius.circular(50)
                  )
                ),
                onPressed: () {},
                label: const Text("Share Achivements", style: TextStyle(color: Colors.white, fontWeight: FontWeight.bold)),
                icon: Tab(icon: Image.asset("assets/instagram.png")),
              ),
            ),
            BadgeList(title: "Unlocked Badges", achievements: provider.achievements.where((element) => !element.isLocked).toList()),
            const SizedBox(height: 30),
            BadgeList(title: "Locked Badges", achievements: provider.achievements.where((element) => element.isLocked).toList())
          ],
        )
      )
    );
  }
}
