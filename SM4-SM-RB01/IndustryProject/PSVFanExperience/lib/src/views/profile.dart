import 'package:flutter/material.dart';

import 'package:psv_fan_experience/src/widgets/background_container.dart';
import 'package:psv_fan_experience/src/widgets/user_submissions.dart';
import 'package:psv_fan_experience/src/widgets/section_title.dart';
import 'package:psv_fan_experience/src/widgets/user_awards.dart';
import 'package:psv_fan_experience/src/widgets/user_widget.dart';
import 'package:psv_fan_experience/src/widgets/user_stats.dart';
import 'package:psv_fan_experience/src/widgets/psv_appbar.dart';
import 'package:psv_fan_experience/src/models/user.dart';

class ProfilePage extends StatelessWidget {
  const ProfilePage({super.key, required this.user});

  final User user;

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: const PSVAppbar(title: 'PROFILE'),
      body: SingleChildScrollView(
        child: Background(
          color: 'red',
          child: Padding(
            padding: const EdgeInsets.all(20.0),
            child: Column(
              mainAxisAlignment: MainAxisAlignment.start,
              crossAxisAlignment: CrossAxisAlignment.start,
              children: [
                UserWidget(
                  profileUrl: user.userProfilePicture,
                  fullname: user.username
                ),
                const SizedBox(height: 30),
                UserStats.from(user.stats),
                const SizedBox(height: 32),
                const SectionTitle(title: 'AWARDS'),
                const SizedBox(height: 16),
                const UserAwards(
                  award1: 'assets/images/Award1.png',
                  award2: 'assets/images/Award2.png'
                ),
                const SizedBox(height: 32),
                const SectionTitle(title: 'SUBMISSIONS'),
                const SizedBox(height: 16),
                UserSubmissions(
                  image: 'https://i.guim.co.uk/img/media/3fa6fbb9f821db2c8c6973ee738d5e1cacb11df0/145_169_3211_1927/master/3211.jpg?width=1200&height=900&quality=85&auto=format&fit=crop&s=e93551f181ef7ab1c487fc316b33d27d'
                )
              ],
            ),
          ),
        ),
      ),
    );
  }
}
