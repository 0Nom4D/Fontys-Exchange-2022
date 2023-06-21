import 'package:flutter/material.dart';

class UserProfile extends StatelessWidget {
  final String userImage;
  final String userIcon;
  final String username;
  final String competitionName;
  final double fem;
  final double ffem;

  const UserProfile({
    Key? key,
    required this.userImage,
    required this.userIcon,
    required this.username,
    required this.competitionName,
    required this.fem,
    required this.ffem,
  }) : super(key: key);

  @override
  Widget build(BuildContext context) {
    return Container(
      margin: EdgeInsets.fromLTRB(0 * fem, 0 * fem, 0 * fem, 16 * fem),
      padding: EdgeInsets.fromLTRB(8 * fem, 7 * fem, 0 * fem, 0 * fem),
      width: double.infinity,
      decoration: BoxDecoration(
        borderRadius: BorderRadius.circular(18 * fem),
        image: DecorationImage(
          fit: BoxFit.cover,
          image: AssetImage(
            userImage,
          ),
        ),
      ),
      child: Column(
        crossAxisAlignment: CrossAxisAlignment.end,
        children: [
          Container(
            margin: EdgeInsets.fromLTRB(0 * fem, 0 * fem, 191 * fem, 224 * fem),
            width: 148 * fem,
            height: 50 * fem,
            child: Stack(
              children: [
                Positioned(
                  left: 35 * fem,
                  top: 11 * fem,
                  child: Align(
                    child: SizedBox(
                      width: 113 * fem,
                      height: 29 * fem,
                      child: Image.asset(
                        'assets/images/rectangle-68.png',
                        width: 113 * fem,
                        height: 29 * fem,
                      ),
                    ),
                  ),
                ),
                Positioned(
                  left: 0 * fem,
                  top: 0 * fem,
                  child: Align(
                    child: SizedBox(
                      width: 50 * fem,
                      height: 50 * fem,
                      child: Image.asset(
                        userIcon,
                        fit: BoxFit.cover,
                      ),
                    ),
                  ),
                ),
                Positioned(
                  left: 55 * fem,
                  top: 17 * fem,
                  child: Align(
                    child: SizedBox(
                      width: 66 * fem,
                      height: 16 * fem,
                      child: Text(
                        username,
                        style: TextStyle(
                          fontSize: 12 * ffem,
                          fontWeight: FontWeight.w700,
                          height: 1.2575 * ffem / fem,
                          color: const Color(0xffffffff),
                        ),
                      ),
                    ),
                  ),
                ),
              ],
            ),
          ),
          //COMPETITION NAME
          Container(
            width: 133 * fem,
            height: 30 * fem,
            decoration: const BoxDecoration(
              image: DecorationImage(
                fit: BoxFit.cover,
                image: AssetImage(
                  'assets/images/rectangle-69.png',
                ),
              ),
            ),
            child: Center(
              child: Text(
                competitionName,
                style: TextStyle(
                  fontSize: 15 * ffem,
                  fontWeight: FontWeight.w700,
                  height: 1.2575 * ffem / fem,
                  color: const Color(0xffffffff),
                ),
              ),
            ),
          ),
        ],
      ),
    );
  }
}
